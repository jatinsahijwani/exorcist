# Demo video script (~2 minutes)

Setup before recording: terminal at the repo root, font size large, `make build` already run (so
nothing compiles on camera), `clear`. Optional second pane with `docs/EXAMPLE_PR.md` / the PR page.

| Time | On screen | Say |
|---|---|---|
| 0:00–0:12 | Title card: "Exorcist — finds ghost funds in NEAR contracts, or proves there are none" | "On NEAR, a cross-contract call can fail after your contract already updated its ledger. Nothing rolls back. That's how ghost funds happen." |
| 0:12–0:25 | Slide or README section "The problem" (3 lines) | "With NEP-141, if the receiver's promise fails, the token refunds the sender. If the receiver already credited the deposit, the credit stays. On Oct 1 this pattern created $3.8M of unbacked balances in NEAR Intents." |
| 0:25–0:55 | `./.lake/build/bin/exorcist check deposit-vulnerable` — scroll to the trace | "Exorcist explores every ordering of receipts and every failure. In 444 states it finds this 5-step attack: eve deposits 100 with a notification to her own hook, the hook fails, the token refunds her, and the vault still owes her 100. The ledger says 200, the vault holds 100." Point at `⚠ INSOLVENT`. |
| 0:55–1:05 | Same output, the "Witness theorem … ✓ checked by the Lean kernel" line, then `cat out/deposit-vulnerable.witness.lean` briefly | "That trace isn't just printed. It's a Lean theorem, re-run and checked by the Lean kernel." |
| 1:05–1:20 | `make sandbox` output already captured, or run `cd sandbox && cargo test --test replay deposit_attack -- --nocapture` (pre-compiled) | "And it's real: the same transactions against Rust contracts in a NEAR sandbox. Eve ends with 200 tokens, the vault with 0, and alice's 100 is gone." |
| 1:20–1:35 | Show the one-line fix in `Verifier/Models/Vault.lean` (credit in `after_notify` only on success); `exorcist check deposit-fixed` → "NO VIOLATION — bounded to depth 10: 1,044,233 states" | "The fix: credit in the callback, only if the notification succeeded. The bounded search finds nothing in a million states, but that's still a bound." |
| 1:35–1:52 | `./.lake/build/bin/exorcist prove deposit-fixed` → "✓ PROVEN FOR ALL TRACES", axioms line | "So we prove it. For any accounts, any amounts, attacker contracts, and any receipt failing, the vault is solvent after every trace. The kernel checks it, with no sorry and no native_decide." |
| 1:52–2:00 | PR #1 page with the red check, or `docs/EXAMPLE_PR.md` | "Run it in CI and a pull request that brings the bug back fails with the attack trace. Tests show a bug exists; proofs show none exist. Repo link below." |

Commands, in order:
```sh
./.lake/build/bin/exorcist check deposit-vulnerable
cat out/deposit-vulnerable.witness.lean
(cd sandbox && cargo test --test replay deposit_attack_on_vulnerable_vault -- --nocapture)
./.lake/build/bin/exorcist check deposit-fixed
./.lake/build/bin/exorcist prove deposit-fixed
```
