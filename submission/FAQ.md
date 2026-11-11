# Exorcist — hard questions, direct answers

**1. Why should I trust the model?**
You should not trust it blindly, and Exorcist does not ask you to. Every semantic rule is sourced in
`docs/SEMANTICS.md` (near-sdk-rs 5.30.1 source, NEAR docs, nomicon). The NEP-141 model follows the
reference `ft_resolve_transfer` line by line, including the edge cases (unparseable result → full
refund, refund capped by the receiver's balance). Then the model is tested against reality: every
trace is replayed against Rust contracts in the NEAR sandbox, and balances, ledger entries and
receipt outcomes are compared after every transaction. All 8 replays match, and a negative control
shows the harness catches wrong predictions.

**2. What if the Rust differs from the model?**
Then the proof is about the model, not your Rust. Today models are written by hand (with AI help) and
reviewed; the sandbox replay checks agreement on the replayed traces only. Automatic extraction from
near-sdk Rust is the main roadmap item. We say this in the README limits, not in small print.

**3. How does it scale?**
Bounded search grows exponentially with depth: depth 10 is 0.4K–11M states and runs in 0.5–16 s for
the examples. It is meant for finding short attacks, which these bugs have (5–6 steps). Scale comes
from the proof, which has no bound: it covers any number of accounts, any amounts, any trace length.
The proof effort is per contract pattern. The generic parts (failures, refunds, fresh receipts,
promise redirection) are reusable; the per-method cases are what changes.

**4. What is the trusted base?**
The Lean 4 kernel and Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`, printed by
`#print axioms`). There is no `sorry` and no `native_decide`, so the Lean compiler is not trusted for any
theorem. Beyond that: the faithfulness of the semantics and token model, and the statement of the
invariant. The explorer and the AI loop are not trusted; their output is re-checked by the kernel.

**5. Why not fuzzing?**
Fuzzing samples executions. The bug needs a specific combination: a deposit with a notification, a
failure of one particular receipt, and an ordering in which the resolve runs after it. Exorcist
enumerates every interleaving and every failure up to the bound, so if a short attack exists in the
scenario it is found, and the shortest one is printed. For the fix, a proof covers all traces, which
no amount of fuzzing can.

**6. How is this different from tests?**
Tests show that a bug exists; proofs show that none exists. A test checks the executions someone
thought of. The explorer checks all executions up to a bound, and the proof checks all executions,
including the attacker's own contracts and failures of any receipt. We still use tests: the sandbox
replay is how we test the model itself.

**7. How do I apply it to my contract?**
Run `exorcist new mycontract`. It scaffolds a model in which each method is `state → call →
(new state, created promises, return value)`, about 20 lines for a deposit/withdraw contract. Then run
`exorcist check mycontract` for a bounded search and `exorcist prove mycontract --bounded 4` for a
kernel-checked bounded result. docs/WRITE-A-MODEL.md walks through it, including a real double-payout
bug, and is tested end to end. An unbounded proof for a new contract still needs an invariant; the
structural lemmas in `Verifier/Proof/` carry over. Add the GitHub Action so every PR is checked.

**8. What do the AI loops do?**
`exorcist prove <model> --ai` sends the goal theorem with its proof removed to a model on NEAR AI
Cloud. Lean checks each proposal, and errors go back to the model for up to N rounds. Proposals that
change the statement or use `sorry`/`native_decide`/axioms are rejected before Lean runs. It is a
convenience: the committed proofs are checked offline without any key, and nothing the AI produces
is trusted unless the kernel accepts it. Today it targets the model-level theorems; the large
invariant proof was written by hand with AI assistance. `exorcist draft --from lib.rs` (experimental)
has NEAR AI draft the model itself from Rust; `make drafts` compares each draft semantically with the
hand-written model. Real drafts need a key and have not been generated yet; only the pipeline is tested,
against a mock.

**9. Isn't "any receipt may fail" unrealistic?**
For the proof it is deliberately the strongest assumption: if the vault stays solvent when the
adversary can fail any receipt, it stays solvent when receipts fail for real reasons (gas, panics,
attacker code). For finding attacks we use weaker, realistic adversaries: only the attacker's own
contract fails (deposit), or only non-callback receipts fail (withdraw). Each result states which.

**10. What does "bounded to depth 10" cover exactly?**
Five actors (alice, eve, token, vault, hook); alice has 100 credited, eve holds 100 tokens; four
transactions (two deposits by eve, one with a notification, and a withdraw each by eve and alice),
each at most once, in any order; every interleaving of ready receipts; failures as allowed by the
stated adversary; up to 10 steps. The CLI prints this with every result.

**11. Would this have caught the Oct 1 NEAR Intents exploit? Does it verify the Intents contract?**
It does not verify the Intents contract; we did not model it. `incident-2026-10` is a minimal model,
written from scratch, of the mechanism the postmortem describes: a depositor-chosen contract is
notified, the notification is made to fail, the token refunds, the ledger credit stays. Asked only
"can the attacker cash out more than she put in?", the explorer finds the full deposit → fail → refund →
withdraw exploit in 26,191 states (~50 ms), and the fixed version is proven for all traces. The postmortem also notes that monitoring never compared
aggregate internal balances with tokens held, which is the invariant Exorcist checks and proves.

**12. Why Lean 4, why no Mathlib, why `decide`?**
Lean gives a small kernel and a computable language, so the same definitions run the explorer and are
reasoned about in proofs. No Mathlib keeps a judge's build at about 2 minutes. `decide` makes the
kernel itself re-run each concrete trace, while `native_decide` would trust the compiler; we use
`decide` everywhere.

**13. Why an MCP server, and why does it matter for security?**
AI agents increasingly write and deploy contracts, and an agent with deploy rights will not notice an
async accounting bug in its own code. The MCP gate gives the agent `exorcist_check` and
`exorcist_prove`, whose results include `deploy_allowed`; the policy is "deploy only on true". The
scripted test (`mcp/agent_gate_demo.py`) shows a vulnerable contract blocked and its fix allowed. The
gate is only as good as the model, so a model the agent writes for itself must be reviewed by a human.

**Bonus: what about per-user correctness, not just solvency?**
Solvency is the property whose violation drains other users, and the one the exploit broke. The
second property, "no stuck funds" (a failed payout must not burn the user's balance), is also proven
for all traces (`fixed_vault_no_stuck_funds`): whenever nothing is in flight, the vault holds exactly
what the ledger owes. It assumes callbacks are not failed (gas reserved) and no plain `ft_transfer`
donations to the vault, and the README states both assumptions.
