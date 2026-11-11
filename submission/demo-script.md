# Demo video script (~2 minutes)

Setup before recording: terminal at the repo root, large font, `make build` already run, `clear`.
Have the GitHub PR #1 page or `docs/EXAMPLE_PR.md` open in a second window. The animated
`docs/media/demo.svg` can serve as b-roll.

| Time | On screen | Say |
|---|---|---|
| 0:00–0:10 | Title card: "Exorcist — finds ghost funds in NEAR contracts, or proves there are none" | "On October 1st, an attacker drained 3.8 million dollars of unbacked balances from NEAR Intents, using a cross-contract call that was made to fail on purpose." |
| 0:10–0:22 | README, "The opening case" box (the quote from the postmortem) | "The postmortem describes the mechanism: a deposit notifies a contract the attacker controls, the notification fails, the token refunds the deposit, and the ledger keeps the credit. We wrote a minimal model of that mechanism. It is not their contract." |
| 0:22–0:55 | `./.lake/build/bin/exorcist check incident-2026-10`, then scroll the trace | "We don't tell Exorcist what the attack is. We only ask whether an attacker can ever take out more than she put in. It tries every ordering of receipts and every failure, and in 26 thousand states, in about 50 milliseconds, it finds the whole exploit: deposit 100, fail the notification, get refunded, keep the credit, withdraw it. Eve ends with 200." Point at `⚠ INSOLVENT` and `eve=200`. |
| 0:55–1:05 | The "✓ checked by the Lean kernel" line; briefly `cat out/incident-2026-10.witness.lean` | "This isn't a log line. The trace is a Lean theorem, checked by the Lean kernel." |
| 1:05–1:20 | `(cd sandbox && cargo test --test replay deposit_attack -- --nocapture)` (pre-compiled) | "And it happens on real NEAR: in the sandbox, against Rust contracts, the attack does exactly what the model predicted, after every transaction." |
| 1:20–1:42 | The one-line fix in `Verifier/Models/Vault.lean` (credit in `after_notify`, only on success); `./.lake/build/bin/exorcist prove incident-2026-10-fixed` → "✓ PROVEN FOR ALL TRACES" | "The fix: credit only after the notification succeeds. Testing could only show the bug is gone in the cases we tried. This is a proof: for any accounts, any amounts, any attacker contract, and any receipt failing, the vault stays solvent. Checked by the kernel, with no sorry." |
| 1:42–1:53 | `python3 mcp/agent_gate_demo.py` (last lines: BLOCKED … allowed) | "AI agents ship contracts now. Through an MCP server, the agent may deploy only what Exorcist accepts. Vulnerable: blocked. Fixed: allowed." |
| 1:53–2:00 | PR #1 with the red check, then the repo URL | "In CI, a PR that brings the bug back fails with the attack trace. Tests show a bug exists; proofs show none exist. Link below." |

Commands, in order:
```sh
./.lake/build/bin/exorcist check incident-2026-10
cat out/incident-2026-10.witness.lean
(cd sandbox && cargo test --test replay deposit_attack_on_vulnerable_vault -- --nocapture)
./.lake/build/bin/exorcist prove incident-2026-10-fixed
python3 mcp/agent_gate_demo.py
```
