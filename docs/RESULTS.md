# Results

Every row is labelled either **bounded to depth N** (exhaustive search, but only up to N steps in the
scenario below) or **proven for all traces** (a Lean theorem, checked by the kernel, no step bound).
Regenerate everything with `make demo`.

## Summary

| Model | Contract | Result | Label | Kernel-checked artefact |
|---|---|---|---|---|
| `incident-2026-10` | **minimal model of the Oct 2026 NEAR Intents mechanism, not their contract**: credits on deposit, notifies a depositor-chosen contract, returns its promise | **full exploit found automatically**: eve cashes out 200 from a 100 deposit (26,191 states, ~45 ms) | found at depth 8 | generated witness; `Witness/Incident.lean`: `incident_repeated_theft` (two failed deposits → eve 300, pool backed by 100) |
| `incident-2026-10-fixed` | credits only after the notification succeeded | no violation (1,289,374 states); **solvent** | bounded to depth 10; **proven for all traces** | `concrete_fixed_solvent_from`; `incident_repeated_fixed_safe` |
| `deposit-vulnerable` | credits in `ft_on_transfer`, returns the hook's promise | **attack found**: insolvent after 5 steps (444 states) | found within depth 10 | `Witness/GhostFunds.lean`: `ghost_funds_insolvent`, `ghost_funds_theft` |
| `deposit-fixed` | credits in `after_notify`, only on success | no violation (1,044,233 states) | bounded to depth 10 | — |
| `deposit-fixed` | same | **solvent** | **proven for all traces** | `Proof/Theorem.lean`: `fixed_vault_solvent_forever` |
| `noreturn-vulnerable` | as deposit-vulnerable, hook returns nothing | **attack found with no failure at all**: insolvent after 5 steps (438 states) | found within depth 10 | `Witness/NoReturn.lean`: `no_return_insolvent` |
| `noreturn-fixed` | fixed vault, same hook | no violation (839,929 states) | bounded to depth 10 | — |
| `noreturn-fixed` | same | **solvent** | **proven for all traces** | `fixed_vault_solvent_forever` |
| `withdraw-vulnerable` | debits, `ft_transfer`, never restores on failure | **funds stuck** after 5 steps (3,622 states) | found within depth 10 | `Witness/WithdrawNoRestore.lean`: `withdraw_funds_stuck` |
| `withdraw-fixed` | restores the ledger in `after_withdraw` on failure | no violation (11,154,645 states) | bounded to depth 10 | `withdraw_fixed_restores` (the attack trace, replayed) |
| `withdraw-fixed` | same | **solvent** | **proven for all traces** | `fixed_vault_solvent_forever` |
| `withdraw-fixed` | same | **no stuck funds** (tokens held = Σ ledger whenever nothing is in flight), **assuming callbacks don't fail and no plain `ft_transfer` donations** | **proven for all traces** (under those assumptions) | `Proof/NoStuckCases.lean`: `fixed_vault_no_stuck_funds` |
| `withdraw-fixed-callback-fail` | the fixed vault, but the adversary may also fail callbacks | **funds stuck** after 4 steps (167 states): the token's `ft_resolve_transfer` runs out of gas, so a deposit stays uncredited. Solvency still holds | found at depth 4: shows the no-stuck assumption is necessary | generated witness |
| `noreturn-fixed` | fixed vault, hook returns nothing | **no stuck funds** (same assumptions) | **proven for all traces** (under those assumptions) | `concrete_no_stuck` |

The fixes are not vacuous: `Witness/Liveness.lean` proves (kernel, `decide`) for both fixed
configurations that an honest deposit through a succeeding hook is credited and that withdraw pays
out real tokens. `exorcist check` also searches for these goals with no forced failures and reports
them as reachable.

## Bounds of every bounded result

| | |
|---|---|
| Depth | up to 10 steps; a step = submit one transaction, run one ready receipt, or make one ready receipt fail |
| Actors | alice (user), eve (attacker, owns the hook), token (NEP-141), vault, hook |
| Amounts | initial: alice has 100 credited in the vault, eve holds 100 tokens, the vault holds 100 |
| Transactions | each at most once, in any order: eve `ft_transfer_call(vault, 100, "notify hook")`, eve `ft_transfer_call(vault, 100, "")`, eve `withdraw(100)`, alice `withdraw(100)` |
| Orderings | every interleaving of ready receipts |
| Adversary — deposit models | receipts on eve's own contract (the hook) may fail |
| Adversary — noreturn models | nothing is forced to fail (only real panics) |
| Adversary — withdraw models | any non-callback receipt may fail (too little gas, unregistered receiver, …); callbacks are assumed to have gas reserved |
| Invariant | solvency: Σ ledger ≤ tokens held by the vault, in every state; and no stuck funds: tokens held ≤ Σ ledger whenever nothing is in flight |

## What "proven for all traces" covers

`fixed_vault_solvent_forever` (`Verifier/Proof/Theorem.lean`):

* any account type and any number of accounts; token at any `T`, vault at any `V ≠ T`;
* any amounts; any initial state with nothing in flight and `Σ ledger ≤ tokens held`;
* traces of any length and any interleaving of ready receipts;
* **any** receipt may be failed by the adversary (`canFail` is arbitrary);
* arbitrary code on every other account (attacker contracts, the hook) — it may emit any calls but
  cannot write the token's or the vault's storage;
* transactions with any call and arguments from any account except `T` and `V`;
* both withdraw variants and any hook return value (the theorem assumes only `depositFixed = true`).

Conclusion: in every reachable state, `Σ ledger ≤ token balance of V`.

`concrete_fixed_solvent` instantiates it for the explorer's five-actor model, for every adversary.

`fixed_vault_no_stuck_funds` (`Verifier/Proof/NoStuckCases.lean`) has the same generality, with three
extra, explicit assumptions: both fixes are in place; the adversary fails only non-callback receipts
(callbacks have gas reserved); and nobody sends the vault tokens with a plain `ft_transfer` (a donation
would legitimately be owed to no one). From an initial state where the ledger equals the vault's
balance, every reachable state has tokens held ≤ Σ ledger + in-flight amounts, and tokens held = Σ ledger
whenever nothing is in flight. `concrete_no_stuck` instantiates it for `withdraw-fixed` and
`noreturn-fixed`. Its invariant adds exact pairing: every pending callback with potential waits on
exactly one in-flight source of the same amount.

## Agent gate, user models, drafts

| What | Result | Label |
|---|---|---|
| MCP agent gate (`mcp/agent_gate_demo.py`) | `withdraw-vulnerable` blocked (attack trace returned), `withdraw-fixed` allowed after `check` + `prove` | tested in CI and `make demo` |
| `exorcist new` walkthrough (`scripts/test-walkthrough.sh`) | scaffold clean (8,251,651 states) and kernel-checked to depth 4; the "debit on success" variant pays alice twice (found at depth 8) | tested in CI |
| `exorcist prove <model> --bounded N` | the bounded search re-run inside the kernel (`decide +kernel`) | kernel-checked, bounded |
| `exorcist draft` (EXPERIMENTAL) | NEAR AI drafted all 3 contracts (5 builds); all compile in round 1; 8/8 semantic checks match the hand-written models; human review: all faithful, and the drafts model a near-sdk deposit rule we had omitted ([drafts/ASSESSMENT.md](../drafts/ASSESSMENT.md)) | experimental; evidence on 3 contracts |

## Sandbox validation (near-workspaces 0.24, local NEAR sandbox)

`sandbox/tests/replay.rs` deploys the Rust token, hook and vault variants and replays the exported
traces transaction by transaction. After every transaction it asserts that all token balances and
ledger entries equal the model's prediction, and that the receipts that ran (and which failed) equal
the model's receipts.

| Test | Result |
|---|---|
| `happy_path_fixed_vault` (deposit via hook, withdraw) | matches the model |
| `happy_path_fixed_vault_noreturn_hook` | matches the model |
| `deposit_attack_on_vulnerable_vault` (+ eve cashes out 100) | matches: eve ends with 200, vault 0, alice's ledger 100 |
| `deposit_attack_fails_on_fixed_vault` | matches: nothing credited, eve's withdraw panics |
| `noreturn_attack_on_vulnerable_vault` | matches |
| `noreturn_attack_fails_on_fixed_vault` | matches |
| `withdraw_without_restore_on_vulnerable_vault` | matches: alice's ledger 0, vault keeps 100 |
| `withdraw_restores_on_fixed_vault` | matches: alice's ledger restored to 100 |
| `harness_detects_model_mismatch` (negative control) | the harness fails when predictions are wrong |

No mismatch between model and sandbox was found.

## Testnet replay: run on 2026-11-11

The ghost-funds attack (`deposit-vulnerable`, plus eve's cash-out) was replayed on **NEAR testnet**
against the vulnerable and the fixed vault, using a dedicated, faucet-sponsored testnet account
(`exorcist-replay-35b9fa.testnet`). After every transaction the chain state matched the Lean model.

| | Vulnerable vault | Fixed vault |
|---|---|---|
| vault contract | [vault-x404319v](https://testnet.nearblocks.io/address/vault-x404319v.exorcist-replay-35b9fa.testnet) | [vault-x404319f2](https://testnet.nearblocks.io/address/vault-x404319f2.exorcist-replay-35b9fa.testnet) |
| tx1: eve `ft_transfer_call(vault, 100, "notify hook")`, hook made to fail | [EBigWS13…](https://testnet.nearblocks.io/txns/EBigWS13rHHqTDYNKMsamY9d4bhcdpuR4v1GFUkMxycN): refunded **and** credited | [G9f5oowA…](https://testnet.nearblocks.io/txns/G9f5oowAE1Y1tmjBR1ePsAxmPtdSdtZ6aYcYkuPKppqG): refunded, not credited |
| tx2: eve `withdraw(100)` | [qSjvAX1o…](https://testnet.nearblocks.io/txns/qSjvAX1otfxW8iBi2SJ9ebh5cMcYqhry2ftW5Wo3czm): **pays out 100** | [FNioJzWa…](https://testnet.nearblocks.io/txns/FNioJzWavui9B3AN4jqMkuL5FUUQeTz2RYzaPjDDCDzV): panics (no balance) |
| final state | eve 200 tokens, vault **0**, alice's ledger still 100 | eve 100, vault 100, alice's ledger 100 |

Shared contracts: [token](https://testnet.nearblocks.io/address/token-x404319.exorcist-replay-35b9fa.testnet),
[hook](https://testnet.nearblocks.io/address/hook-x404319.exorcist-replay-35b9fa.testnet). The fixed vault
was replayed in a second invocation (`EXORCIST_TESTNET_REUSE=x404319 EXORCIST_TESTNET_ONLY=fixed`)
after the public RPC rate-limited the first one. The test accounts' keys are kept outside the repository.

## Axioms (`#print axioms`)

```
'NearAsync.Vault.Proof.fixed_vault_solvent_forever' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearAsync.Vault.Proof.concrete_fixed_solvent' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearAsync.Vault.Witness.ghost_funds_insolvent' depends on axioms: [propext]
'NearAsync.Vault.Witness.ghost_funds_theft' depends on axioms: [propext]
'NearAsync.Vault.Witness.fixed_attack_fails' depends on axioms: [propext]
'NearAsync.Vault.Witness.no_return_insolvent' depends on axioms: [propext]
'NearAsync.Vault.Witness.withdraw_funds_stuck' depends on axioms: [propext]
'NearAsync.Vault.Witness.withdraw_fixed_restores' depends on axioms: [propext]
'NearAsync.Vault.Witness.fixed_deposit_is_credited' depends on axioms: [propext]
'NearAsync.Vault.Witness.fixed_withdraw_pays_out' depends on axioms: [propext]
'NearAsync.Vault.Proof.fixed_vault_no_stuck_funds' depends on axioms: [propext, Classical.choice, Quot.sound]
'NearAsync.Vault.Proof.concrete_no_stuck' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`propext`, `Classical.choice` and `Quot.sound` are Lean's standard axioms. No `sorryAx`, and no
`Lean.ofReduceBool`: **`native_decide` is not used anywhere**. Witness theorems are proved by `decide`.
