# "What we built" (submission field `idea`, 20–2000 characters)

Exorcist finds ghost funds in NEAR contracts, or proves there are none. On a minimal model of the Oct 2026 NEAR Intents mechanism (our own code, not their contract), it finds the full exploit automatically: deposit, deliberately failed notification, token refund, kept ledger credit, cash-out. It takes 8 steps, 26,191 states and about 45 ms, and the trace is checked by the Lean kernel. The fixed version is proven solvent for every trace of our NEAR execution model.

The problem: NEAR cross-contract calls are asynchronous. Each receipt commits on its own, and a later failure never rolls back earlier state. With NEP-141, if a receiver credits a deposit and the call chain then fails, the token refunds the sender while the credit stays. In the Oct 2026 incident this produced $3.8M of unbacked balances.

What we built: a Lean 4 model of NEAR async execution and the NEP-141 transfer/resolve flow, plus:
- a bounded explorer over every receipt ordering and failure, which prints the shortest attack and re-checks it in the Lean kernel (4 bug patterns found);
- unbounded Lean proofs: the fixed vault is solvent for every trace (any accounts, amounts, attacker contracts, receipt failures), and leaves no funds stuck, assuming callbacks don't fail and no plain ft_transfer donations. No sorry, no native_decide;
- validation against real Rust contracts: 8 sandbox replays match the model after every transaction, and on NEAR testnet the attack drains the vulnerable vault and leaves the fixed one whole;
- an MCP gate so AI coding agents can deploy only contracts that pass, a GitHub Action that fails PRs reintroducing the bug, `exorcist new` to model your own contract, and experimental NEAR AI drafting of models from Rust (all three drafts matched).

How NEAR fits: it targets NEAR's execution model specifically and runs in the NEAR sandbox and on testnet. Its AI loops use NEAR AI Cloud. `make demo` reproduces everything; a claims table in the README maps each claim to a command.
