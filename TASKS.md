# Task list — Exorcist (go mode, single session, 11 Nov 2026)

- [x] Day-1 core: semantics, NEP-141 token, vault models, bounded explorer, kernel-checked witness
- [x] Private GitHub repo, small conventional commits, push after each
- [x] Rename CLI to `exorcist`
- [x] 1. Fixes not vacuous: liveness theorems (decide) + explorer liveness goals for every fixed config
- [x] 2. Honest bounds in CLI output and docs/RESULTS.md (depth, actors, amounts, adversary)
- [x] 3. Unbounded proof: `fixed_vault_solvent_forever` (any accounts, amounts, failures, attacker code); axioms printed
- [x] 4. Withdraw-without-restore pattern: trace + witness (vulnerable); liveness + bounded + solvency proof (fixed)
- [x] 4b. Unbounded "no stuck funds" proof: `fixed_vault_no_stuck_funds` (assumes non-callback failures, no donations)
- [x] 5. No-return-value variant: named finding, trace + witness
- [x] 6. `exorcist check --json`, readable trace, auto witness file, exit codes
- [x] 7. Sandbox: Rust token/vault/hook, 8 replays + negative control, all match the model
- [x] 8. `exorcist prove` offline + `--ai` NEAR AI Cloud loop (live round untested: no key)
- [x] 9. GitHub workflow + reusable action.yml + example vulnerable PR (#1, check fails as intended)
- [x] 10. Testnet replay script (not run; needs Jatin's testnet account + key)
- [x] 11. make demo / make quick, pinned toolchains (lean-toolchain, rust-toolchain.toml, Cargo.lock)
- [x] 12. Facts verified with sources (leadership "release process" claim NOT confirmed → softened)
- [x] 13. README, SEMANTICS, RESULTS, ARCHITECTURE, EXAMPLE_PR, LICENSE
- [ ] 13b. Q-015 disclosure line — need Jatin's other project name
- [x] 14. submission/: FAQ, demo-script, x-post, outreach (payload.json after Jatin's answers)
- [x] 15. Fresh-clone subagent check (clean; wording fixes applied); live HACKATHON.md unchanged (11 Nov)
- [ ] Jatin: answers for payload fields; yes for public repo / X post / submission

## Round 2 (make the submission stronger)
- [x] 1. Incident reconstruction: `incident-2026-10` (minimal model, not their contract) found automatically (depth 8, 26,191 states); fixed version proven; in make demo / README / demo script
- [x] 2. Agent gate: MCP server (exorcist_check / exorcist_prove), docs/AGENT-GATE.md, tested (make test-mcp, CI, demo)
- [x] 3. `exorcist new` + docs/WRITE-A-MODEL.md; walkthrough tested end to end (scripts/test-walkthrough.sh, CI); `prove --bounded N` kernel-checked
- [x] 4. `exorcist draft` EXPERIMENTAL: real NEAR AI drafts of all 3 contracts committed; 8/8 checks match; human review in drafts/ASSESSMENT.md
- [x] 5. Animated demo (asciicast + SVG) at README top; static results page docs/site + manual Pages workflow (Pages not enabled)
- [x] 6. FAQ, demo script, x-post, what-we-built updated
- [x] 7. Fresh-clone check (clean; fixes applied)
