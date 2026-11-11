import Verifier
import Verifier.Report
import Exorcist.Prove

open NearAsync NearAsync.Vault

structure Opts where
  model : String := ""
  depth : Nat := 10
  json : Option String := none     -- "-" = stdout
  emitLean : Option String := none
  verify : Bool := true

def parseCheck : List String → Opts → Except String Opts
  | [], o => .ok o
  | "--depth" :: n :: rest, o => match n.toNat? with
    | some d => parseCheck rest { o with depth := d }
    | none => .error s!"bad depth {n}"
  | "--json" :: f :: rest, o =>
    if f.startsWith "--" then parseCheck (f :: rest) { o with json := some "-" }
    else parseCheck rest { o with json := some f }
  | ["--json"], o => .ok { o with json := some "-" }
  | "--emit-lean" :: f :: rest, o => parseCheck rest { o with emitLean := some f }
  | "--no-verify" :: rest, o => parseCheck rest { o with verify := false }
  | m :: rest, o =>
    if o.model = "" && !m.startsWith "--" then parseCheck rest { o with model := m }
    else .error s!"unexpected argument {m}"

def usage : String :=
  "exorcist — finds ghost funds in NEAR contracts, or proves there are none.\n\n" ++
  "usage:\n" ++
  "  exorcist list\n" ++
  "  exorcist check <model> [--depth N] [--json [FILE]] [--emit-lean FILE] [--no-verify]\n" ++
  "  exorcist prove <model> [--ai] [--rounds N] [--ai-model ID]\n\n" ++
  "models: " ++ ", ".intercalate (models.map (·.name))

def menuText : List String :=
  menu.map fun (sg, rv, c, d) => s!"{sg} → {rv}.{showCall c}" ++ (if d > 0 then s!" +{d} yocto" else "")

def boundsText (m : Model) (depth : Nat) : List String :=
  [ s!"  depth:      up to {depth} steps (a step = submit a tx, run a receipt, or fail a receipt)",
    s!"  actors:     alice (user), eve (attacker, owns hook), token (NEP-141), vault, hook",
    s!"  amounts:    alice has 100 credited in the vault; eve holds 100 tokens; vault holds 100",
    s!"  txs:        each at most once, in any order: " ++ "; ".intercalate menuText,
    s!"  adversary:  {m.adv.describe}",
    s!"  orderings:  every interleaving of ready receipts" ]

def boundsJson (m : Model) (depth : Nat) : String :=
  jObj [ ("depth", toString depth),
         ("actors", jArr (Acct.all.map (jStr ·.name))),
         ("adversary", jStr m.adv.describe),
         ("transactions", jArr (menuText.map jStr)),
         ("each_tx_at_most_once", "true") ]

/-- Kernel-check a generated witness file with the pinned Lean (via lake). -/
def verifyWitness (file : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", file] }
    if out.exitCode == 0 then return true
    IO.eprintln out.stdout; IO.eprintln out.stderr; return false
  catch e =>
    IO.eprintln s!"could not run lake to check the witness: {e}"; return false

def traceJson (rs : List Row) : String := jArr (rs.map (·.json))

def check (o : Opts) : IO UInt32 := do
  let some m := findModel o.model
    | do IO.eprintln s!"unknown model '{o.model}'\n\n{usage}"; return 2
  let quiet := o.json == some "-"
  let say (s : String) : IO Unit := if quiet then pure () else IO.println s
  let sys := system m.cfg m.adv
  say s!"model:      {m.name} — {m.pattern}"
  say s!"contract:   {m.summary}"
  say s!"invariant:  solvency (Σ ledger ≤ tokens held by vault, in every state) and"
  say s!"            no stuck funds (tokens held ≤ Σ ledger whenever nothing is in flight)"
  say "bounds:"
  for l in boundsText m o.depth do say l
  say s!"initial:    {snapshot init}"
  let r := explore { sys, init, menu, ok := accounting } o.depth
  -- liveness: honest use must still work (no forced failures)
  let honest := system m.cfg .none
  let live := goals.map fun g => (g, reach honest init g.txs g.holds 12)
  let mut code : UInt32 := 0
  let mut violationJson := "null"
  match r.trace with
  | none =>
    say s!"\nRESULT: NO VIOLATION — bounded to depth {o.depth}: {r.visited} states explored, all orderings and failure outcomes above."
    say "        This is a bounded result, not a proof for all traces."
    if let some p := m.proof then say s!"        Unbounded proof for this contract: {p} (run: exorcist prove {m.name})"
    if m.vulnerable then code := 4
  | some t =>
    let rs := rows sys init t
    let final := (rs.getLast?.map (·.after)).getD init
    say s!"\nRESULT: VIOLATION ({violationKind final}) at depth {r.depth}, {r.visited} states explored. Shortest attack trace:\n"
    for l in renderText rs do say l
    let file := o.emitLean.getD s!"out/{m.name}.witness.lean"
    IO.FS.createDirAll (System.FilePath.mk file).parent.get!
    IO.FS.writeFile file (witnessSource m t final)
    say s!"\nWitness theorem: {file}"
    if o.verify then
      if ← verifyWitness file then say "  ✓ checked by the Lean kernel (decide): this trace really violates the invariant"
      else do IO.eprintln "  ✗ witness did not check — this is a bug in exorcist"; code := 5
    violationJson := jObj [("kind", jStr (violationKind final)), ("depth", toString r.depth),
                           ("witness_file", jStr file), ("trace", traceJson rs)]
    if code == 0 then code := 1
  say "\nliveness (no forced failures — honest use must still work):"
  let mut liveJson : List String := []
  for (g, lr) in live do
    match lr.trace with
    | some t =>
      say s!"  ✓ reachable in {lr.depth} steps: {g.name}"
      liveJson := liveJson ++ [jObj [("goal", jStr g.name), ("reachable", "true"),
                                     ("trace", traceJson (rows honest init t))]]
    | none =>
      say s!"  ✗ NOT reachable within 12 steps: {g.name}"
      liveJson := liveJson ++ [jObj [("goal", jStr g.name), ("reachable", "false"), ("trace", "[]")]]
      if !m.vulnerable && code == 0 then code := 3
  if let some f := o.json then
    let doc := jObj [ ("tool", jStr "exorcist"), ("model", jStr m.name), ("pattern", jStr m.pattern),
                      ("vulnerable_expected", toString m.vulnerable),
                      ("bounds", boundsJson m o.depth), ("initial_state", jState init),
                      ("states_explored", toString r.visited),
                      ("verdict", jStr (if r.trace.isSome then "violation" else s!"no_violation_bounded_to_depth_{o.depth}")),
                      ("violation", violationJson), ("liveness", jArr liveJson) ]
    if f == "-" then IO.println doc else do
      IO.FS.writeFile f doc; say s!"\nJSON written to {f}"
  return code

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
    for m in models do
      IO.println s!"{m.name.pushn ' ' (22 - m.name.length)}{if m.vulnerable then "vulnerable" else "fixed     "}  {m.pattern}: {m.summary}"
    return 0
  | "check" :: rest =>
    match parseCheck rest {} with
    | .ok o => check o
    | .error e => do IO.eprintln s!"{e}\n\n{usage}"; return 2
  | "prove" :: rest => Exorcist.prove rest
  | _ => do IO.println usage; return (if args.isEmpty || args == ["--help"] then 0 else 2)
