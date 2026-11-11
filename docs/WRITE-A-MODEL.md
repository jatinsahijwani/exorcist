# Write a model of your own contract (about 20 lines)

This walkthrough models a small savings contract, checks it, finds a classic NEAR async bug in a
plausible variant, and kernel-checks the fixed one. It is tested end to end by
`scripts/test-walkthrough.sh` (in a throwaway copy of the repo, also run in CI).

## 1. Scaffold

```sh
./.lake/build/bin/exorcist new savings
lake build exorcist
```

```
created Verifier/Models/User/Savings.lean and registered model 'savings' in Verifier/Models/User.lean
next:
  lake build exorcist
  ./.lake/build/bin/exorcist check savings
  ./.lake/build/bin/exorcist prove savings --bounded 4
```

The contract lives in `Verifier/Models/User/Savings.lean`. The part you edit is `handle`, one case
per method. A method returns `.ok newState [promises it creates] result` or `.panic reason`:

```lean
def handle (ctx : Ctx Acct) (c : Call Acct) (s : St Acct) : Outcome (St Acct) Acct (Call Acct) :=
  match c with
  | .ft_on_transfer sender amt _ =>
    if ctx.pred ≠ .token then .panic "only the token" else
    .ok { s with ledger := s.ledger.add sender amt } [] (.val (.nat 0))   -- credit; 0 unused
  | .withdraw amt =>
    if amt = 0 ∨ s.ledger.get ctx.pred < amt then .panic "insufficient balance" else
    .ok { s with ledger := s.ledger.sub ctx.pred amt }                    -- debit first
      [ { recv := .token, call := .ft_transfer ctx.pred amt, deposit := 1 },
        { recv := .vault, call := .after_withdraw ctx.pred amt, after := some 0 } ] (.val .unit)
  | .after_withdraw who amt =>
    if ctx.pred ≠ ctx.self then .panic "private" else
    match ctx.input with
    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val .unit)  -- restore
    | _ => .ok s [] (.val .unit)
  | _ => .panic "method not found"
```

`ctx` holds `pred` (caller), `self`, `deposit` and, in a callback, `input` (the result of the promise it
waited on: `some (.ok v)` or `some .failed`). A promise is `{ recv, call, deposit, after }`, where
`after := some i` means "`.then` of the i-th promise created by this call". Below `handle` the file
wires the contract next to the NEP-141 token model, lists the transactions the explorer may send (an
outside deposit by eve, two withdrawals by alice, one by eve), and states the property: *alice never
receives more than her 100, and whenever nothing is in flight the ledger is backed.*

## 2. Check it and get a kernel-checked bounded result

```sh
./.lake/build/bin/exorcist check savings
./.lake/build/bin/exorcist prove savings --bounded 4
```

```
RESULT: NO VIOLATION — bounded to depth 10: 8251651 states explored in 8868 ms, all orderings and failure outcomes above.
        This is a bounded result, not a proof for all traces.

liveness (no forced failures — honest use must still work):
  ✓ reachable in 4 steps: alice withdraws her 100

kernel-checking: no violation in any trace of ≤ 4 steps (out/bounded-savings.lean) …
RESULT:    ✓ KERNEL-CHECKED, BOUNDED TO DEPTH 4 (not a proof for all traces)
axioms:    'savings_bounded_4' depends on axioms: [propext]
```

`check` is an exhaustive search (8.25M states here). `prove --bounded N` re-runs the search
*inside the Lean kernel* (`decide +kernel`), so the bounded result no longer trusts compiled code. It
is still bounded: keep N small (4–5), because kernel evaluation is slow. An unbounded proof for a new
contract needs an inductive invariant; `Verifier/Proof/` has the one for the built-in vault.

## 3. Introduce a common bug and watch it get caught

A tempting "optimisation" is to debit only once the payout succeeded, in the callback:

```diff
   | .withdraw amt =>
     if amt = 0 ∨ s.ledger.get ctx.pred < amt then .panic "insufficient balance" else
-    .ok { s with ledger := s.ledger.sub ctx.pred amt }                    -- debit first
+    .ok s                                                                  -- BUG: no debit here
       [ ... ft_transfer ..., ... after_withdraw ... ] (.val .unit)
   | .after_withdraw who amt =>
     ...
-    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val .unit)  -- restore
+    | some (.ok _) => .ok { s with ledger := s.ledger.sub who amt } [] (.val .unit)  -- debit on success
```

```sh
lake build exorcist && ./.lake/build/bin/exorcist check savings
```

```
RESULT: VIOLATION (insolvent) at depth 8, 121612 states explored in 191 ms. Shortest attack trace:

1. eve sends tx: token.ft_transfer_call(vault, 100, "") (+1 yocto)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=0 eve=100
2. run #0 token.ft_transfer_call(vault, 100, "")  ⇒ returns a promise
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
3. alice sends tx: vault.withdraw(100)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
4. run #3 vault.withdraw(100)  ⇒ ok (no value)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
5. run #4 token.ft_transfer(alice, 100)  ⇒ ok (no value)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=100 eve=0
6. alice sends tx: vault.withdraw(100)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=100 eve=0
7. run #6 vault.withdraw(100)  ⇒ ok (no value)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=100 eve=0
8. run #7 token.ft_transfer(alice, 100)  ⇒ ok (no value)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=0 alice=200 eve=0   ⚠ INSOLVENT (ledger > tokens held)

Witness theorem: out/savings.witness.lean
  ✓ checked by the Lean kernel (decide): this trace really violates the property
```

Exit code 1. Alice's second withdrawal passes the balance check before the first callback has
debited her, so she is paid twice — the second time with eve's deposit. The trace is re-checked by the
kernel in `out/savings.witness.lean`. Revert the change and `check` is clean again.

## Tips

* Use the built-in actors (`alice`, `eve`, `token`, `vault`, `hook`) and calls (`Call` in
  `Verifier/Token.lean`); add constructors there if your contract needs new methods.
* `adv := .nonCallback` lets the adversary fail any non-callback receipt; `.anyReceipt` is stronger.
* Change `txs`, `init` and `prop` in the scaffolded `model` to fit your scenario. `exorcist check
  <name> --json` gives machine-readable output, and the MCP gate (docs/AGENT-GATE.md) works for user
  models too.
