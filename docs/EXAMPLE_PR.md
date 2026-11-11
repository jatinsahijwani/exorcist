# Example: a pull request that reintroduces ghost funds

Draft PR [#1](https://github.com/jatinsahijwani/exorcist/pull/1) (branch `example/vulnerable-pr`,
kept open as a demonstration, never to be merged) changes one line of the fixed vault:

```diff
   | .after_notify who amt =>
     if ctx.pred ≠ ctx.self then .panic "private method" else
     match ctx.input with
     | some (.ok _) => .ok { s with ledger := s.ledger.add who amt } [] (.val (.nat 0))
-    | some .failed => .ok s [] (.val (.nat amt))   -- all unused: token refunds, nothing credited
+    -- notifications are best-effort: credit the deposit even if the hook failed
+    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val (.nat amt))
```

It looks harmless, but the callback still reports the whole amount as unused, so the token refunds
the depositor while the ledger keeps the credit.

## What the Exorcist check reports on that PR

`exorcist check deposit-fixed` (exit code 1, the job fails):

```
RESULT: VIOLATION (insolvent) at depth 6, 1720 states explored in 1 ms. Shortest attack trace:

1. eve sends tx: token.ft_transfer_call(vault, 100, "notify hook") (+1 yocto)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=0 eve=100
2. run #0 token.ft_transfer_call(vault, 100, "notify hook")  ⇒ returns a promise
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
3. run #1 vault.ft_on_transfer(eve, 100, "notify hook")  ⇒ returns a promise
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
4. FAIL #3 hook.on_deposit(eve, 100)  ⇒ adversary makes it fail
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
5. run #4 vault.after_notify(eve, 100)  ⇒ ok, returns 100
     ledger: alice=100 eve=100 (total 200) | tokens: vault=200 alice=0 eve=0
6. run #2 token.ft_resolve_transfer(eve, vault, 100)  ⇒ ok, returns 0  — refunds 100 vault → eve
     ledger: alice=100 eve=100 (total 200) | tokens: vault=100 alice=0 eve=100   ⚠ INSOLVENT (ledger > tokens held)

Witness theorem: out/deposit-fixed.witness.lean
  ✓ checked by the Lean kernel (decide): this trace really violates the property
```

The unbounded proof stops compiling at the exact case that broke (`lake build`):

```
error: Verifier/Proof/Solvency.lean:282:12: omega could not prove the goal:
```

That line is the `after_notify` failure case: the ledger grows while the potential refund does not shrink.
