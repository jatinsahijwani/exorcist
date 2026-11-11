# Exorcist

**Finds ghost funds in NEAR contracts, or proves there are none.**

Exorcist checks whether a NEAR contract can lose money when a cross-contract call fails. For a
vulnerable contract it prints a concrete, step-by-step attack trace and a Lean theorem, checked by the
Lean kernel, stating that the trace really breaks the invariant. For a fixed contract it gives an
exhaustive bounded search result and a Lean 4 proof that the invariant holds for **every** trace.
Every trace is also replayed against real Rust contracts in a local NEAR sandbox.

## The problem

NEAR cross-contract calls are asynchronous. Every receipt commits on its own; when a later receipt
fails, earlier state changes are **not** rolled back. With NEP-141 tokens this has a sharp edge:
`ft_transfer_call` moves the tokens, calls the receiver's `ft_on_transfer`, and then
`ft_resolve_transfer` **refunds the sender** if that call — or the promise it returned — failed, or
did not return a number.

So a receiver that credits its internal ledger and then hands the token a promise that can fail
(for example a notification to a contract the depositor controls) can be made to credit a deposit
that is refunded. Repeat, then withdraw: the "ghost" balance is paid out from other users' tokens.
Tests usually cover the happy path, not every combination of orderings and failures.

This is the mechanism NEAR Intents' postmortem describes for the exploit of Sept 29 – Oct 1, 2026:
"The attacker created a contract that deliberately failed those notifications, causing the token
contract to refund the deposit while NEAR Intents retained the corresponding ledger credit", building
$3.8M of unbacked balances over 23 failed deposits; the funds were returned. The postmortem also notes
that monitoring "did not compare users' aggregate internal balances with the tokens actually held" —
the invariant Exorcist checks. ([cryptonews summary of the Oct 16 postmortem](https://cryptonews.net/news/security/33604900/))

## What Exorcist does

1. **A model of NEAR async execution in Lean 4** (`Verifier/Async.lean`): receipts, promises,
   `.then` callbacks with `PromiseResult` (success/failure), per-receipt commit with no cross-receipt
   rollback, promise return, deposit refunds to the predecessor, any order of ready receipts.
   Each rule is sourced in [docs/SEMANTICS.md](docs/SEMANTICS.md).
2. **NEP-141 token model** (`Verifier/Token.lean`) following the near-sdk-rs 5.30.1 reference
   implementation, including `ft_resolve_transfer`'s `min(unused, receiver balance)` refund.
3. **Contract models** as `state → call → (new state, emitted calls, return)`
   (`Verifier/Models/Vault.lean`): a deposit-ledger vault with two bug patterns and their fixes.
4. **Bounded explorer** (`exorcist check`): every interleaving and every receipt failure up to depth N.
   It prints the shortest attack trace, a JSON file with the expected balances after every step, and a
   generated witness `.lean` file that the Lean kernel checks immediately.
5. **Unbounded proof** (`exorcist prove`): an inductive invariant proving that the fixed vault is solvent
   after every trace, with any accounts, any amounts, arbitrary attacker contracts and **any** receipt
   failures (`Verifier/Proof/`).
6. **Sandbox validation**: Rust versions of the token, vault variants and hook, and near-workspaces tests that
   replay every trace and compare the chain state to the model after every transaction.
7. **CI**: a GitHub Action that fails a pull request when a deployed contract's model has a violation.

## Quickstart

Prerequisites: `git`, `curl`, `python3`; [elan](https://github.com/leanprover/elan) (the Lean toolchain
manager; it installs the pinned Lean 4.34.0 automatically); for the sandbox part, [rustup](https://rustup.rs)
(it installs the pinned Rust 1.96.0 and the wasm target automatically).

```sh
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y --default-toolchain none
git clone https://github.com/jatinsahijwani/exorcist && cd exorcist
```

**1. Fast screening, no sandbox** (about 2 minutes on a laptop; the first run also downloads Lean):

```sh
make quick
```

You should see a table that ends like this:

```
PASS    deposit-vulnerable: attack found, witness theorem kernel-checked          found at depth 5
PASS    noreturn-vulnerable: attack found, witness theorem kernel-checked         found at depth 5
PASS    withdraw-vulnerable: attack found, witness theorem kernel-checked         found at depth 5
PASS    deposit-fixed: no violation, honest deposit + withdraw reachable          bounded to depth 10
PASS    noreturn-fixed: no violation, honest deposit + withdraw reachable         bounded to depth 10
PASS    withdraw-fixed: no violation, honest deposit + withdraw reachable         bounded to depth 10
PASS    deposit-fixed: solvent (sum of ledger <= tokens held)                     proven for all traces
PASS    noreturn-fixed: solvent (sum of ledger <= tokens held)                    proven for all traces
PASS    withdraw-fixed: solvent (sum of ledger <= tokens held)                    proven for all traces
PASS    withdraw-fixed: no stuck funds                                            bounded to depth 10 (no unbounded proof yet)
PASS    sandbox replay skipped (QUICK=1)                                          -

ALL PASS
```

**2. See the attack:**

```sh
./.lake/build/bin/exorcist check deposit-vulnerable
```

```
RESULT: VIOLATION (insolvent) at depth 5, 444 states explored. Shortest attack trace:

1. eve sends tx: token.ft_transfer_call(vault, 100, "notify hook") (+1 yocto)
     ledger: alice=100 eve=0 (total 100) | tokens: vault=100 alice=0 eve=100
2. run #0 token.ft_transfer_call(vault, 100, "notify hook")  ⇒ returns a promise
     ledger: alice=100 eve=0 (total 100) | tokens: vault=200 alice=0 eve=0
3. run #1 vault.ft_on_transfer(eve, 100, "notify hook")  ⇒ returns a promise
     ledger: alice=100 eve=100 (total 200) | tokens: vault=200 alice=0 eve=0
4. FAIL #3 hook.on_deposit(eve, 100)  ⇒ adversary makes it fail
     ledger: alice=100 eve=100 (total 200) | tokens: vault=200 alice=0 eve=0
5. run #2 token.ft_resolve_transfer(eve, vault, 100)  ⇒ ok, returns 0  — refunds 100 vault → eve
     ledger: alice=100 eve=100 (total 200) | tokens: vault=100 alice=0 eve=100   ⚠ INSOLVENT (ledger > tokens held)

Witness theorem: out/deposit-vulnerable.witness.lean
  ✓ checked by the Lean kernel (decide): this trace really violates the invariant
```

The exit code is 1. Before the result it prints the exact bounds (depth, actors, amounts,
transactions, which receipts the adversary may fail); after it, the same transactions replayed on the
fixed vault, and the liveness checks. Add `--json FILE` for machine-readable output with the expected
balances and ledger after every step.

**3. See the proof of the fix:**

```sh
./.lake/build/bin/exorcist prove deposit-fixed
```

```
RESULT:    ✓ PROVEN FOR ALL TRACES (checked by the Lean kernel now, file out/prove-deposit-fixed.lean)
axioms:    'deposit_fixed_solvent_all_traces' depends on axioms: [propext, Classical.choice, Quot.sound]
axioms:    'NearAsync.Vault.Proof.fixed_vault_solvent_forever' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**4. Everything, including the real-contract sandbox replay** (the first run compiles the Rust
dependencies, about 10 minutes; later runs about 3 minutes):

```sh
make demo
```

This adds rows such as `PASS  sandbox: deposit_attack_on_vulnerable_vault  matches model step by step`
for each of the 9 sandbox tests, and ends with `ALL PASS`.

Other commands: `exorcist list` (all models), `make check` (CI gate), `make prove`, `make sandbox`.

## Results

| Model | Result | Label |
|---|---|---|
| `deposit-vulnerable` | insolvent after 5 steps; eve can then withdraw alice's tokens | found within depth 10, witness kernel-checked |
| `deposit-fixed` | no violation (1,044,233 states) | bounded to depth 10 |
| `deposit-fixed` | solvent | **proven for all traces** |
| `noreturn-vulnerable` | insolvent after 5 steps **without any failure** (hook returns nothing) | found within depth 10, witness kernel-checked |
| `noreturn-fixed` | no violation (839,929 states); solvent | bounded to depth 10; **proven for all traces** |
| `withdraw-vulnerable` | user's tokens stuck in the vault after a failed payout | found within depth 10, witness kernel-checked |
| `withdraw-fixed` | no violation (11,154,645 states); solvent | bounded to depth 10; **proven for all traces** |
| `withdraw-fixed` | no stuck funds | bounded to depth 10 only |
| sandbox | all 8 trace replays match the model after every transaction | real Rust contracts, near-workspaces |

Details, bounds and `#print axioms` output: [docs/RESULTS.md](docs/RESULTS.md).
A pull request that reintroduces the bug, and the failing check: [docs/EXAMPLE_PR.md](docs/EXAMPLE_PR.md).

## How NEAR fits

* **Async receipts.** The model is NEAR's execution model: independent receipts, `.then` callbacks
  that always run, `PromiseResult::Failed`, promise return, no cross-receipt rollback, deposit refunds
  to the predecessor.
* **NEP-141.** The token model and the Rust token follow the near-sdk-rs reference
  `ft_transfer_call` / `ft_on_transfer` / `ft_resolve_transfer` flow, which is where the refund that
  creates ghost funds comes from.
* **near-workspaces sandbox and testnet.** Model predictions are checked against real contracts in the
  NEAR sandbox; `scripts/testnet-replay.sh` runs the same attack on NEAR testnet.
* **NEAR AI Cloud.** `exorcist prove <model> --ai` runs a proof-repair loop on NEAR AI Cloud's
  OpenAI-compatible API (`https://cloud-api.near.ai/v1`, key from `NEARAI_API_KEY`). `prove` works
  without a key using the committed proofs.

## What exactly is proven

`NearAsync.Vault.Proof.fixed_vault_solvent_forever`: for any account type, token `T` and vault
`V ≠ T`, any code on all other accounts (it may emit any calls but cannot write the token's or the
vault's storage), any set of receipts the adversary may fail, any transactions with any arguments and
amounts from accounts other than `T` and `V`, and any initial state with nothing in flight and a backed
ledger: after every finite trace, `Σ ledger ≤ tokens held by V`. It holds for both withdraw variants
and any hook (it assumes only that deposits are credited in the callback).

The invariant (`Verifier/Proof/Defs.lean`): Σ ledger + every refund that a pending
`ft_resolve_transfer` may still make + every amount a pending `after_withdraw` may still restore
≤ tokens held. It also requires well-formed pending receipts: fresh, distinct ids, and every in-flight
credit or vault transfer has its callback waiting on it for at least that amount.

## Limits

* **The models are written by hand** (with AI assistance) from the Rust contracts and reviewed by a
  human. Exorcist does not yet read Rust; automatic extraction is on the roadmap. If the Rust differs
  from the model, the proof says nothing about the Rust. The sandbox replay is how we check that they
  agree on the traces we run.
* **Proofs are only as good as the specification and the semantics model.** The invariant is solvency
  of the vault's ledger. The semantics follows NEAR docs and the near-sdk-rs reference (sources in
  docs/SEMANTICS.md).
* **Not modelled:** gas (instead the adversary may fail receipts; the proof allows any receipt to
  fail), storage staking and NEP-145 registration (every account is treated as registered), deleted
  accounts (the reference token burns refunds to deleted senders), u128 overflow (amounts are unbounded
  naturals), `promise_set_refund_to`, joint promises (`and`).
* **Bounded results are bounded.** "No violation up to depth 10" covers the listed actors, amounts and
  transactions only. Only rows labelled "proven for all traces" are unbounded.
* "No stuck funds" for the withdraw pattern is bounded only; the unbounded proof covers solvency.
* The example contracts are small and written for this project; they are not production contracts.

## Trusted base

* The Lean 4 kernel (v4.34.0) and Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`).
  No `sorry`, no `native_decide` (witnesses use `decide`), so the compiler is not trusted for any theorem.
* The faithfulness of `Verifier/Async.lean` and `Verifier/Token.lean` to NEAR and NEP-141, and of
  the vault model to the Rust vault. The sandbox replay checks this on the replayed traces, not in general.
* The statement of the invariant (read `Verifier/Proof/Defs.lean` and `Theorem.lean`).
* Not trusted: the explorer (its traces are re-checked by the kernel) and the AI loop (its proposals
  are checked by Lean, and rejected if they change the statement or use `sorry`/`native_decide`/axioms).

## Repository layout

| Path | What |
|---|---|
| `Verifier/Async.lean` | NEAR async semantics |
| `Verifier/Token.lean` | NEP-141 token model |
| `Verifier/Models/` | vault variants, hook, registry of models and liveness goals |
| `Verifier/Explore.lean` | bounded explorer |
| `Verifier/Witness/` | kernel-checked witness and liveness theorems |
| `Verifier/Proof/` | unbounded solvency proof |
| `Main.lean`, `Exorcist/Prove.lean` | `exorcist` CLI (`check`, `prove`, `--ai`) |
| `sandbox/` | Rust contracts, replay library, near-workspaces tests, testnet binary |
| `scripts/` | `demo.sh`, `testnet-replay.sh` |
| `action.yml`, `.github/workflows/` | reusable GitHub Action and this repo's CI |
| `docs/` | semantics, results, architecture, example PR |

## Testnet replay

```sh
export EXORCIST_TESTNET_ACCOUNT=you.testnet          # needs about 13 testnet NEAR
export EXORCIST_TESTNET_PRIVATE_KEY=ed25519:...      # keep out of the repo
scripts/testnet-replay.sh
```

It deploys the token, hook, vulnerable and fixed vaults under your account, replays the attack against
both, checks the chain state against the model after every transaction, and prints
`testnet.nearblocks.io` links. It refuses to run if the account or RPC is not testnet.

## Using it in another repository

```yaml
- uses: jatinsahijwani/exorcist@main
  with:
    models: deposit-fixed withdraw-fixed
    depth: "10"
    prove: "true"
```

Models are compiled into the tool: to check your own contract, add a model under `Verifier/Models/`,
register it in `Registry.lean`, and point the action's `path` input at your fork.

## Libraries and tools

Lean 4 v4.34.0 (core only, no Mathlib) · Rust 1.96.0 · near-sdk 5.30.1 · near-workspaces 0.24.0 ·
tokio, serde, serde_json, anyhow · NEAR AI Cloud API (optional) · elan, lake, cargo.
The code was written during the hackathon with AI coding assistance (Claude Code) and reviewed by the author.

## Hackathon window

All code in this repository was written during NEAR HACKATHON, starting 2026-11-11 (Q-001). There is
no pre-hackathon baseline. Libraries and AI assistance are listed above (Q-005).

## Tracks

`security` (AI Security & Defense) and `open` (Open Innovation).

## Roadmap

* Extract models from Rust contracts automatically (near-sdk method bodies to the contract DSL).
* Unbounded proof of "no stuck funds" (an exact-accounting invariant) for the withdraw pattern.
* More patterns: NEP-171/245 transfers with callbacks, multi-token vaults, `promise_and` joins.
* Model gas explicitly (callback gas reservations) instead of arbitrary failures.
* Use the AI repair loop for the invariant proof of new contracts, not only the model-level corollaries.

## Background facts

* NEAR Intents exploit: see "The problem" above and the
  [postmortem summary](https://cryptonews.net/news/security/33604900/).
* NEAR AI's Lean agent solved all 672 PutnamBench problems (670 upstream plus corrected versions of two
  flawed ones) for about $112 of model cost ([nearai/putnambench-deepseek](https://github.com/nearai/putnambench-deepseek)).
* NEAR has announced that it is next applying AI-assisted formal verification to "the NEAR protocol and
  core smart contracts" ([crypto.news](https://crypto.news/near-ai-formal-verification-protocol-smart-contracts/)).

## License

MIT, see [LICENSE](LICENSE).
