import Lean.Data.Json
import Verifier.Models.All
import Verifier.Report

/-!
# `exorcist prove <model>`

Default (offline, no key): states the model's "solvent for all traces" theorem in a fresh file and
has Lean check its committed proof, then prints the axioms it depends on.

`--ai`: proof-repair loop on NEAR AI Cloud (OpenAI-compatible chat API). The goal file is sent
with its proof replaced by `sorry`; the model proposes a complete file; Lean checks it; compiler
errors go back to the model; up to `--rounds N` rounds. Proposals that change the statement or use
`sorry`/`admit`/`native_decide`/new axioms are rejected without running Lean. Every round is logged
under `out/ai/`. The key is read from `NEARAI_API_KEY` only and is never written to disk logs.
-/

namespace Exorcist

open Lean NearAsync NearAsync.Vault

def defaultBaseUrl : String := "https://cloud-api.near.ai/v1"

/-- NEAR AI Cloud; `EXORCIST_AI_BASE_URL` overrides it (used by the offline mock test). -/
def getBaseUrl : IO String := do
  return (← IO.getEnv "EXORCIST_AI_BASE_URL").getD defaultBaseUrl

/-- Preferred models, used only if present in the live `/v1/models` list. -/
def preferred : List String :=
  ["anthropic/claude-opus-5-5", "anthropic/claude-sonnet-5-5", "openai/gpt-5.5", "deepseek/deepseek-v4.1-flash"]

structure ProveOpts where
  model : String := ""
  ai : Bool := false
  rounds : Nat := 5
  aiModel : Option String := none
  json : Bool := false
  bounded : Option Nat := none

def parse : List String → ProveOpts → Except String ProveOpts
  | [], o => .ok o
  | "--ai" :: r, o => parse r { o with ai := true }
  | "--rounds" :: n :: r, o => match n.toNat? with
    | some k => parse r { o with rounds := k }
    | none => .error s!"bad --rounds {n}"
  | "--ai-model" :: m :: r, o => parse r { o with aiModel := some m }
  | "--json" :: r, o => parse r { o with json := true }
  | "--bounded" :: n :: r, o => match n.toNat? with
    | some k => parse r { o with bounded := some k }
    | none => .error s!"bad --bounded {n}"
  | m :: r, o => if o.model == "" && !m.startsWith "--" then parse r { o with model := m } else .error s!"unexpected {m}"

def theoremName (m : Model) : String := s!"{m.name.replace "-" "_"}_solvent_all_traces"

/-- The goal: this model's fixed vault is solvent after every trace, under its adversary. -/
def goalHeader (m : Model) : String :=
  s!"import Verifier\nopen NearAsync NearAsync.Vault\n\n" ++
  s!"/-- {m.name}: every trace from `init`, any length, any interleaving, adversary `{leanAdv m.adv}`,\n" ++
  s!"transactions from anyone but the two contracts: the vault stays solvent. -/\n" ++
  s!"theorem {theoremName m} (tr : Tr) (hsg : Proof.honestSigners Acct.token Acct.vault tr)\n" ++
  s!"    (w : W) (hrun : run (system {leanCfg m.cfg} {leanAdv m.adv}) {m.initLean} tr = some w) :\n" ++
  s!"    solvent w = true := by\n"

def committedProof (m : Model) : String :=
  s!"  exact Proof.concrete_fixed_solvent_from _ rfl _ {m.initLean} ⟨rfl, rfl, by decide⟩ tr hsg w hrun\n"

/-- Models whose adversary fails only non-callback receipts also get the no-stuck-funds theorem. -/
def noStuckApplies (m : Model) : Bool := m.noStuck

def noStuckGoal (m : Model) : String :=
  s!"\n/-- {m.name}: whenever nothing is in flight, every token the vault holds is owed to someone\n" ++
  s!"(no plain `ft_transfer` to the vault; only non-callback receipts fail). -/\n" ++
  s!"theorem {m.name.replace "-" "_"}_no_stuck_all_traces (tr : Tr)\n" ++
  s!"    (htx : Proof.honestTxs Acct.token Acct.vault tr) (w : W)\n" ++
  s!"    (hrun : run (system {leanCfg m.cfg} {leanAdv m.adv}) {m.initLean} tr = some w) : noStuck w = true :=\n" ++
  s!"  Proof.concrete_no_stuck_from _ rfl rfl _ (fun r h => by simpa [canFail] using h) {m.initLean}\n" ++
  s!"    ⟨rfl, rfl, by decide, by decide⟩ tr htx w hrun\n"

def axiomsFooter (m : Model) : String :=
  s!"\n#print axioms {theoremName m}\n#print axioms NearAsync.Vault.Proof.fixed_vault_solvent_forever\n" ++
  (if noStuckApplies m then
    s!"#print axioms {m.name.replace "-" "_"}_no_stuck_all_traces\n#print axioms NearAsync.Vault.Proof.fixed_vault_no_stuck_funds\n"
   else "")

def runLean (file : String) : IO (Bool × String) := do
  let lake ← do
    let home ← IO.getEnv "HOME"
    let cand := (home.map (· ++ "/.elan/bin/lake")).getD "lake"
    if ← System.FilePath.pathExists cand then pure cand else pure "lake"
  let out ← IO.Process.output { cmd := lake, args := #["env", "lean", file] }
  return (out.exitCode == 0, out.stdout ++ out.stderr)

def forbidden : List String := ["sorry", "admit", "native_decide", "axiom ", "implemented_by", "extern"]

def stripFences (s : String) : String :=
  let ls := s.splitOn "\n"
  let ls := ls.filter fun l => !(l.trimLeft.startsWith "```")
  "\n".intercalate ls

/-- One chat completion via curl. The key goes into a 0600 header file that is deleted at once. -/
def chat (key model : String) (msgs : List (String × String)) : IO (Except String String) := do
  IO.FS.createDirAll "out/ai"
  let body := Json.mkObj [
    ("model", Json.str model),
    ("messages", Json.arr (msgs.toArray.map fun (role, content) =>
      Json.mkObj [("role", Json.str role), ("content", Json.str content)])),
    ("temperature", Json.num 0) ]
  IO.FS.writeFile "out/ai/request.json" body.compress
  let hdr := "out/ai/.auth-header"
  IO.FS.writeFile hdr s!"Authorization: Bearer {key}\n"
  let _ ← IO.Process.output { cmd := "chmod", args := #["600", hdr] }
  let baseUrl ← getBaseUrl
  let out ← IO.Process.output { cmd := "curl", args := #["-sS", "-m", "600",
    s!"{baseUrl}/chat/completions", "-H", "Content-Type: application/json", "-H", s!"@{hdr}",
    "--data", "@out/ai/request.json"] }
  IO.FS.removeFile hdr
  if out.exitCode != 0 then return .error s!"curl failed: {out.stderr}"
  match Json.parse out.stdout with
  | .error e => return .error s!"bad JSON from API: {e}: {out.stdout.take 300}"
  | .ok j =>
    match j.getObjValD "choices" |>.getArrVal? 0 with
    | .ok c => match (c.getObjValD "message").getObjValAs? String "content" with
      | .ok s => return .ok s
      | .error _ => return .error s!"no content in response: {out.stdout.take 300}"
    | .error _ => return .error s!"API error: {out.stdout.take 500}"

def pickModelId (explicit : Option String) : IO (Except String String) := do
  if let some m := explicit then return .ok m
  if let some m ← IO.getEnv "NEARAI_MODEL" then return .ok m
  let baseUrl ← getBaseUrl
  let out ← IO.Process.output { cmd := "curl", args := #["-sS", "-m", "30", s!"{baseUrl}/models"] }
  match Json.parse out.stdout with
  | .error _ => return .error "could not list models; pass --ai-model"
  | .ok j =>
    let ids := match j.getObjValD "data" with
      | .arr a => a.toList.filterMap fun (x : Json) => (x.getObjValAs? String "id").toOption
      | _ => []
    match preferred.find? ids.contains with
    | some m => return .ok m
    | none => return .error s!"none of {preferred} is available; pass --ai-model (available: {ids.take 10} …)"

def system : String :=
  "You are a Lean 4 (v4.34.0, no Mathlib) proof assistant. You receive a Lean file whose proof is " ++
  "`sorry`. Reply with the COMPLETE Lean file and nothing else: keep every line up to and including " ++
  "`:= by` exactly as given, replace `sorry` with a proof. Never use sorry, admit, native_decide, " ++
  "or new axioms. Useful library facts: `NearAsync.Vault.Proof.concrete_fixed_solvent (cfg) " ++
  "(hfix : cfg.depositFixed = true) (adv) (tr) (hsg) (w) (hrun : run (system cfg adv) init tr = some w) : " ++
  "solvent w = true`, and the general `NearAsync.Vault.Proof.fixed_vault_solvent_forever`."

def aiLoop (m : Model) (o : ProveOpts) (key : String) : IO UInt32 := do
  let model ← match ← pickModelId o.aiModel with
    | .ok x => pure x
    | .error e => do IO.eprintln e; return 2
  IO.println s!"AI proof repair on NEAR AI Cloud ({← getBaseUrl}), model {model}, up to {o.rounds} rounds"
  let goal := goalHeader m ++ "  sorry\n"
  let mut msgs : List (String × String) := [("system", system), ("user", goal)]
  for i in [1:o.rounds+1] do
    let reply ← chat key model msgs
    let proposal ← match reply with
      | .ok s => pure (stripFences s)
      | .error e => do IO.eprintln s!"round {i}: {e}"; return 2
    let file := s!"out/ai/{m.name}-round{i}.lean"
    IO.FS.writeFile file proposal
    let bad := forbidden.filter fun f => (proposal.splitOn f).length > 1
    let feedback ←
      if !(proposal.startsWith (goalHeader m)) then
        pure "Rejected: the file must start with exactly the given lines up to and including `:= by`."
      else if !bad.isEmpty then
        pure s!"Rejected: forbidden constructs {bad}."
      else do
        let (ok, out) ← runLean file
        if ok then
          IO.println s!"round {i}: ✓ Lean accepted the proof ({file})"
          let (_, ax) ← do
            IO.FS.writeFile (file ++ ".axioms.lean") (proposal ++ axiomsFooter m)
            runLean (file ++ ".axioms.lean")
          IO.println ax
          return 0
        pure s!"Lean rejected it:\n{out.take 4000}"
    IO.println s!"round {i}: ✗ {feedback.take 200}"
    IO.FS.writeFile (file ++ ".feedback.txt") feedback
    msgs := msgs ++ [("assistant", proposal), ("user", feedback ++ "\nSend the corrected complete file.")]
  IO.println s!"no accepted proof after {o.rounds} rounds (logs in out/ai/)"
  return 1

def jStr' (x : String) : Json := Json.str x

def emit (o : ProveOpts) (m : Model) (verdict : String) (allowed : Bool) (theorems : List String)
    (axioms : List String) (note : String) (file : String := "") : IO Unit := do
  if o.json then
    IO.println (Json.mkObj [
      ("tool", jStr' "exorcist"), ("command", jStr' "prove"), ("model", jStr' m.name),
      ("verdict", jStr' verdict), ("deploy_allowed", Json.bool allowed),
      ("theorems", Json.arr (theorems.toArray.map jStr')),
      ("axioms", Json.arr (axioms.toArray.map jStr')), ("file", jStr' file), ("note", jStr' note) ]).compress

/-- Kernel-checked bounded result: no trace of up to `n` steps violates the model's property. -/
def proveBounded (m : Model) (o : ProveOpts) (n : Nat) : IO UInt32 := do
  IO.FS.createDirAll "out"
  let file := s!"out/bounded-{m.name}.lean"
  let M := m.leanName
  let thm := s!"{m.name.replace "-" "_"}_bounded_{n}"
  IO.FS.writeFile file (
    s!"import {m.leanModule}\nimport Verifier.Explore\nopen NearAsync NearAsync.Vault\n\n" ++
    s!"/-- {m.name}: no trace of at most {n} steps (every interleaving and allowed failure) violates the property.\n" ++
    s!"Checked by the Lean kernel (`decide +kernel`): this re-runs the whole bounded search in the kernel. -/\n" ++
    s!"theorem {thm} :\n    (dfs \{ sys := ({M}).sys, init := ({M}).init, menu := ({M}).menu, ok := ({M}).prop } {n}\n" ++
    s!"      ({M}).init ({M}).menu []).1 = none := by\n  decide +kernel\n\n#print axioms {thm}\n")
  if !o.json then IO.println s!"kernel-checking: no violation in any trace of ≤ {n} steps ({file}) …"
  let (ok, out) ← runLean file
  let axs := (out.splitOn "\n").filter (·.startsWith "'")
  if ok then
    if !o.json then
      IO.println s!"RESULT:    ✓ KERNEL-CHECKED, BOUNDED TO DEPTH {n} (not a proof for all traces)"
      for l in axs do IO.println s!"axioms:    {l}"
    emit o m s!"kernel_checked_bounded_to_depth_{n}" true [thm] axs "bounded result only" file
    return 0
  else
    if !o.json then IO.println s!"RESULT:    ✗ the kernel found a violation within {n} steps, or rejected the file:\n{out.take 2000}"
    emit o m "violation_or_error" false [] [] (out.take 500).toString file
    return 1

def prove (args : List String) : IO UInt32 := do
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  let some m := findModel o.model
    | do IO.eprintln s!"unknown model '{o.model}'"; return 2
  if let some n := o.bounded then return ← proveBounded m o n
  if m.vulnerable then
    if !o.json then
      IO.println s!"{m.name} is vulnerable: there is no proof to check (run `exorcist check {m.name}` for the attack)."
    emit o m "vulnerable" false [] [] s!"run exorcist check {m.name} for the attack trace"
    return 1
  if m.proof.isNone then
    if !o.json then
      IO.println s!"{m.name}: no committed unbounded proof for this model (custom contract)."
      IO.println s!"  Kernel-checked bounded result: exorcist prove {m.name} --bounded 4"
      IO.println s!"  An unbounded proof needs an invariant; see Verifier/Proof/ for the vault's, or try --ai (experimental)."
    emit o m "no_unbounded_proof" false [] [] s!"try: exorcist prove {m.name} --bounded 4"
    return 3
  if o.ai then
    match ← IO.getEnv "NEARAI_API_KEY" with
    | none => IO.eprintln "--ai needs NEARAI_API_KEY in the environment (see https://cloud.near.ai)"; return 2
    | some key => return ← aiLoop m o key
  IO.FS.createDirAll "out"
  let file := s!"out/prove-{m.name}.lean"
  IO.FS.writeFile file (goalHeader m ++ committedProof m ++ (if noStuckApplies m then noStuckGoal m else "") ++ axiomsFooter m)
  if !o.json then
    IO.println s!"model:     {m.name} — {m.pattern}"
    if let some d := m.disclaimer then IO.println s!"NOTE:      {d}"
    IO.println s!"statement: for EVERY trace from init (any length, any interleaving, ANY receipt may fail),"
    IO.println s!"           transactions from any non-contract account: Σ ledger ≤ tokens held by the vault"
    IO.println s!"general:   Proof.fixed_vault_solvent_forever — any accounts, any amounts, any code on other accounts,"
    IO.println s!"           any receipt may fail (Verifier/Proof/*.lean)"
  let (ok, out) ← runLean file
  if !ok then
    if !o.json then IO.eprintln s!"✗ Lean rejected the committed proof:\n{out}"
    emit o m "proof_failed" false [] [] (out.take 500).toString file
    return 1
  let axs := (out.splitOn "\n").filter (·.startsWith "'")
  let thms := [theoremName m] ++ (if noStuckApplies m then [s!"{m.name.replace "-" "_"}_no_stuck_all_traces"] else [])
  if !o.json then
    IO.println s!"RESULT:    ✓ PROVEN FOR ALL TRACES: solvent (checked by the Lean kernel now, file {file})"
    if noStuckApplies m then
      IO.println "           ✓ PROVEN FOR ALL TRACES: no stuck funds (Proof.fixed_vault_no_stuck_funds; assumes no plain"
      IO.println "             ft_transfer to the vault and only non-callback receipts fail)"
    for l in axs do IO.println s!"axioms:    {l}"
  emit o m "proven_all_traces" true thms axs "kernel-checked; no sorry, no native_decide" file
  return 0

end Exorcist
