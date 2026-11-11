# "What we built" (submission field `idea`, 20–2000 characters) — draft for Jatin to edit

Exorcist finds ghost funds in NEAR contracts, or proves there are none.

The problem: NEAR cross-contract calls are asynchronous. Each receipt commits on its own, and a later failure never rolls back earlier state. With NEP-141, if a receiver credits a deposit and the call chain then fails, the token refunds the sender while the credit stays. In the Oct 2026 NEAR Intents incident, this mechanism produced $3.8M of unbacked balances.

What we built: a Lean 4 model of NEAR async execution (receipts, callbacks, promise results, deposit refunds) and of the NEP-141 transfer/resolve flow. On top of it:
- a bounded explorer that tries every receipt ordering and failure and prints the shortest attack trace. Each trace is re-checked by the Lean kernel as a witness theorem. On a minimal model of the incident mechanism (our own code, not their contract), it finds the full exploit automatically in 26,191 states.
- unbounded Lean proofs that the fixed vault stays solvent and never strands user funds, for any accounts, amounts, attacker contracts and receipt failures. No sorry, no native_decide.
- validation of the model against real Rust contracts in the NEAR sandbox: 8 replays match after every transaction.
- an MCP server that lets AI coding agents deploy only contracts that pass, a GitHub Action that fails PRs on violations, `exorcist new` to model your own contract in about 20 lines, and an experimental NEAR AI loop that drafts models from Rust (on our three contracts, every draft matched the hand-written model).

How NEAR fits: Exorcist targets NEAR's execution model specifically (async receipts, NEP-141 refunds). It is validated in the NEAR sandbox (a testnet replay script is included), and its optional AI loops run on NEAR AI Cloud. One command (`make demo`) reproduces everything.
