# Results

Every row is labelled either **bounded to depth N** (exhaustive search, but only up to N steps in the
scenario below) or **proven for all traces** (a Lean theorem, checked by the kernel, no step bound).
Regenerate everything with `make demo`.

## Summary

| Model | Contract | Result | Label | Kernel-checked artefact |
|---|---|---|---|---|
| `deposit-vulnerable` | credits in `ft_on_transfer`, returns the hook's promise | **attack found**: insolvent after 5 steps (444 states) | found within depth 10 | `Witness/GhostFunds.lean`: `ghost_funds_insolvent`, `ghost_funds_theft` |
| `deposit-fixed` | credits in `after_notify`, only on success | no violation (1,044,233 states) | bounded to depth 10 | — |
| `deposit-fixed` | same | **solvent** | **proven for all traces** | `Proof/Theorem.lean`: `fixed_vault_solvent_forever` |
| `noreturn-vulnerable` | as deposit-vulnerable, hook returns nothing | **attack found with no failure at all**: insolvent after 5 steps (438 states) | found within depth 10 | `Witness/NoReturn.lean`: `no_return_insolvent` |
| `noreturn-fixed` | fixed vault, same hook | no violation (839,929 states) | bounded to depth 10 | — |
| `noreturn-fixed` | same | **solvent** | **proven for all traces** | `fixed_vault_solvent_forever` |
| `withdraw-vulnerable` | debits, `ft_transfer`, never restores on failure | **funds stuck** after 5 steps (3,622 states) | found within depth 10 | `Witness/WithdrawNoRestore.lean`: `withdraw_funds_stuck` |
| `withdraw-fixed` | restores the ledger in `after_withdraw` on failure | no violation (11,154,645 states) | bounded to depth 10 | `withdraw_fixed_restores` (the attack trace, replayed) |
| `withdraw-fixed` | same | **solvent** | **proven for all traces** | `fixed_vault_solvent_forever` |
| `withdraw-fixed` | same | no stuck funds | **bounded to depth 10 only** — no unbounded proof yet | — |

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
```

`propext`, `Classical.choice` and `Quot.sound` are Lean's standard axioms. No `sorryAx`, and no
`Lean.ofReduceBool`: **`native_decide` is not used anywhere**. Witness theorems are proved by `decide`.
