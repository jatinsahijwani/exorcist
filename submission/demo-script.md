# Demo video script (~2 minutes)

Setup before recording:
- Browser at 1920×1080, full screen, on the trace viewer:
  https://jatinsahijwani.github.io/exorcist/viewer/ (keys: space play/pause, → step, ← back, v / f switch contract).
  For a clean take you can load `?step=0`; `?model=fixed` opens the fixed view.
- Terminal at the repo root, large font, `make build` already run, `clear`.
- Have the GitHub PR #1 page or `docs/EXAMPLE_PR.md` open in another window.

| Time | On screen | Say |
|---|---|---|
| 0:00–0:08 | Landing page https://jatinsahijwani.github.io/exorcist/ (the pixel EXORCIST wordmark; move the mouse over it) | "On October 1st, an attacker drained 3.8 million dollars of unbacked balances from NEAR Intents, with a cross-contract call made to fail on purpose." |
| 0:08–0:18 | Click "Watch the attack, step by step". Viewer, **Vulnerable**, step 0. Point at the disclaimer line and the four lanes | "This is a minimal model of that mechanism, not their contract. Four contracts: eve the attacker, the token, the vault, and a hook contract eve owns. We never told Exorcist the attack. We only asked: can eve take out more than she put in?" |
| 0:18–0:38 | Press play (1×). Steps 1–5 animate: the deposit, `ft_on_transfer`, the red ✗ on `on_deposit`, then the refund. At step 5 the ledger bar (400) passes the tokens bar (300) and the gap turns red | "Eve deposits 100. The vault credits her. Her own hook fails the notification, on purpose. The token sees the failure and refunds her. But the credit stays: the ledger now owes 400 and the vault holds 300. That red gap is ghost money." |
| 0:38–0:44 | Steps 6–8: withdraw, `ft_transfer`. Point at "eve's tokens: 200 · profit +100" and the VIOLATION pill (depth 8, 26,191 states) | "She withdraws the credit as real tokens. Eve ends with 200. Exorcist found this in 26 thousand states, in about 50 milliseconds." |
| 0:44–0:50 | Press **f** (Fixed). Play through quickly (2×): the ✗ on the notification, the refund, then the withdraw fails in red; the ledger never passes the tokens held. Point at the green "Proven for all traces of our NEAR execution model" badge | "The fix credits only after the notification succeeds. Same attack: the refund happens, the withdraw is rejected, and the ledger never owes more than the vault holds. And this isn't just one run: it's proven for every trace." |
| 0:50–1:02 | Terminal: `./.lake/build/bin/exorcist check incident-2026-10`, scroll to "✓ checked by the Lean kernel"; briefly `cat out/incident-2026-10.witness.lean` | "Everything in that viewer is this command's JSON output. And the trace isn't a log line: it's a Lean theorem, checked by the Lean kernel." |
| 1:02–1:20 | `./.lake/build/bin/exorcist prove incident-2026-10-fixed` → "✓ PROVEN FOR ALL TRACES" | "Testing could only show the bug is gone in the cases we tried. This is a proof: any accounts, any amounts, any attacker contract, any receipt failing, the vault stays solvent. Kernel-checked, no sorry." |
| 1:20–1:35 | `(cd sandbox && cargo test --test replay deposit_attack -- --nocapture)` (pre-compiled) | "And it happens on real NEAR: in the sandbox, against Rust contracts, and on testnet, the attack does exactly what the model predicted, after every transaction." |
| 1:35–1:50 | `python3 mcp/agent_gate_demo.py` (last lines: BLOCKED … allowed) | "AI agents ship contracts now. Through an MCP server, the agent may deploy only what Exorcist accepts. Vulnerable: blocked. Fixed: allowed." |
| 1:50–2:00 | PR #1 with the red check, then the repo URL | "In CI, a PR that brings the bug back fails with the attack trace. Tests show a bug exists; a proof shows none exists in the model. Link below." |

Commands, in order:
```sh
./.lake/build/bin/exorcist check incident-2026-10
cat out/incident-2026-10.witness.lean
(cd sandbox && cargo test --test replay deposit_attack_on_vulnerable_vault -- --nocapture)
./.lake/build/bin/exorcist prove incident-2026-10-fixed
python3 mcp/agent_gate_demo.py
```
