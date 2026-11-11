import Lean.Data.Json
import Verifier.Models.Registry
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

def baseUrl : String := "https://cloud-api.near.ai/v1"

/-- Preferred models, used only if present in the live `/v1/models` list. -/
def preferred : List String :=
  ["anthropic/claude-opus-5-5", "anthropic/claude-sonnet-5-5", "openai/gpt-5.5", "deepseek/deepseek-v4.1-flash"]

structure ProveOpts where
  model : String := ""
  ai : Bool := false
  rounds : Nat := 5
  aiModel : Option String := none

def parse : List String → ProveOpts → Except String ProveOpts
  | [], o => .ok o
  | "--ai" :: r, o => parse r { o with ai := true }
  | "--rounds" :: n :: r, o => match n.toNat? with
    | some k => parse r { o with rounds := k }
    | none => .error s!"bad --rounds {n}"
  | "--ai-model" :: m :: r, o => parse r { o with aiModel := some m }
  | m :: r, o => if o.model == "" && !m.startsWith "--" then parse r { o with model := m } else .error s!"unexpected {m}"

def theoremName (m : Model) : String := s!"{m.name.replace "-" "_"}_solvent_all_traces"

/-- The goal: this model's fixed vault is solvent after every trace, under its adversary. -/
def goalHeader (m : Model) : String :=
  s!"import Verifier\nopen NearAsync NearAsync.Vault\n\n" ++
  s!"/-- {m.name}: every trace from `init`, any length, any interleaving, adversary `{leanAdv m.adv}`,\n" ++
  s!"transactions from anyone but the two contracts: the vault stays solvent. -/\n" ++
  s!"theorem {theoremName m} (tr : Tr) (hsg : Proof.honestSigners Acct.token Acct.vault tr)\n" ++
  s!"    (w : W) (hrun : run (system {leanCfg m.cfg} {leanAdv m.adv}) init tr = some w) :\n" ++
  s!"    solvent w = true := by\n"

def committedProof : String := "  exact Proof.concrete_fixed_solvent _ rfl _ tr hsg w hrun\n"

/-- Models whose adversary fails only non-callback receipts also get the no-stuck-funds theorem. -/
def noStuckApplies (m : Model) : Bool := m.adv == .nonCallback || m.adv == .none

def noStuckGoal (m : Model) : String :=
  s!"\n/-- {m.name}: whenever nothing is in flight, every token the vault holds is owed to someone\n" ++
  s!"(no plain `ft_transfer` to the vault; only non-callback receipts fail). -/\n" ++
  s!"theorem {m.name.replace "-" "_"}_no_stuck_all_traces (tr : Tr)\n" ++
  s!"    (htx : Proof.honestTxs Acct.token Acct.vault tr) (w : W)\n" ++
  s!"    (hrun : run (system {leanCfg m.cfg} {leanAdv m.adv}) init tr = some w) : noStuck w = true :=\n" ++
  s!"  Proof.concrete_no_stuck _ rfl rfl _ (fun r h => by simpa [canFail] using h) tr htx w hrun\n"

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

def pickModel (o : ProveOpts) : IO (Except String String) := do
  if let some m := o.aiModel then return .ok m
  if let some m ← IO.getEnv "NEARAI_MODEL" then return .ok m
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
  let model ← match ← pickModel o with
    | .ok x => pure x
    | .error e => do IO.eprintln e; return 2
  IO.println s!"AI proof repair on NEAR AI Cloud ({baseUrl}), model {model}, up to {o.rounds} rounds"
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

def prove (args : List String) : IO UInt32 := do
  let o ← match parse args {} with
    | .ok o => pure o
    | .error e => do IO.eprintln e; return 2
  let some m := findModel o.model
    | do IO.eprintln s!"unknown model '{o.model}'"; return 2
  if m.vulnerable then
    IO.println s!"{m.name} is vulnerable: there is no proof to check (run `exorcist check {m.name}` for the attack)."
    return 1
  if o.ai then
    match ← IO.getEnv "NEARAI_API_KEY" with
    | none => IO.eprintln "--ai needs NEARAI_API_KEY in the environment (see https://cloud.near.ai)"; return 2
    | some key => return ← aiLoop m o key
  IO.FS.createDirAll "out"
  let file := s!"out/prove-{m.name}.lean"
  IO.FS.writeFile file (goalHeader m ++ committedProof ++ (if noStuckApplies m then noStuckGoal m else "") ++ axiomsFooter m)
  IO.println s!"model:     {m.name} — {m.pattern}"
  IO.println s!"statement: for EVERY trace from init (any length, any interleaving), adversary: {m.adv.describe},"
  IO.println s!"           transactions from any non-contract account: Σ ledger ≤ tokens held by the vault"
  IO.println s!"general:   Proof.fixed_vault_solvent_forever — any accounts, any amounts, any code on other accounts,"
  IO.println s!"           any receipt may fail (Verifier/Proof/*.lean)"
  let (ok, out) ← runLean file
  if !ok then
    IO.eprintln s!"✗ Lean rejected the committed proof:\n{out}"
    return 1
  IO.println s!"RESULT:    ✓ PROVEN FOR ALL TRACES: solvent (checked by the Lean kernel now, file {file})"
  if noStuckApplies m then
    IO.println "           ✓ PROVEN FOR ALL TRACES: no stuck funds (Proof.fixed_vault_no_stuck_funds; assumes no plain"
    IO.println "             ft_transfer to the vault and only non-callback receipts fail)"
  for l in out.splitOn "\n" do
    if l.startsWith "'" then IO.println s!"axioms:    {l}"
  return 0

end Exorcist
