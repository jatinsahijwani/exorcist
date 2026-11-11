# Task list (from BRIEF.md Day 1–4 plan)

## Day 1 — go/no-go (Wed 11 Nov)
- [x] Verify NEP-141 reference impl (near-sdk-rs) + NEAR receipt semantics → docs/SEMANTICS.md
- [x] Lean project skeleton (pinned v4.34.0, no Mathlib)
- [x] Generic async semantics: receipts, promises, callbacks, promise_return, no cross-receipt rollback, deposit refunds
- [x] NEP-141 token model (ft_transfer, ft_transfer_call, ft_resolve_transfer exactly as reference)
- [x] Deposit-ledger vault: vulnerable + fixed
- [x] Bounded explorer (IDDFS over orderings × failures) + readable trace
- [x] Kernel-checked witness theorem for the ghost-funds trace
- [x] Report go/no-go to Jatin

## Day 2
- [ ] Explorer: state dedup (visited set) to push depth past 10
- [ ] Trace text: say "refunds 100 vault → eve" on resolve steps
- [ ] Inductive invariant proof (fixed vault, all traces, any receipt may fail)
- [ ] Readable traces polish
- [ ] near-workspaces sandbox: Rust token + vulnerable/fixed vault; replay trace; attack fails on fixed

## Day 3
- [ ] Withdraw / no-restore pattern (vulnerable + fixed) + proof
- [ ] CLI `check <model> --depth N`, `prove <model>` (+ optional NEAR AI Cloud repair loop, key from env)
- [ ] GitHub Action failing PRs on violation
- [ ] Testnet replay script (testnet only)
- [ ] Verify pitch facts by web search (exploit, leadership statement, PutnamBench) — flag unconfirmed
- [ ] README (machine + human readable, honest limits, libraries), MIT LICENSE

## Day 4
- [ ] `make demo`, ~2-min video script, X post draft
- [ ] Submission payload → show Jatin, wait for yes (no submit/push/public without explicit yes)
