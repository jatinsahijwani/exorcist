import Verifier.Models.Vault

/-! The models `exorcist` knows about. A model is a network (the vault with some switches, or custom
contract code), an adversary, a scenario (initial state + transactions), the property to check, and
the honest-use goals (liveness) that a fix must still allow. -/

namespace NearAsync.Vault

open NearAsync

abbrev TxT := Acct × Acct × Call Acct × Nat

structure Goal where
  name : String
  /-- the only transactions allowed while searching for this goal -/
  txs : List TxT
  holds : W → Bool

/-- Honest deposit with a hook that succeeds ends up credited. -/
def goalDepositCredited : Goal :=
  { name := "honest deposit via ft_transfer_call(\"notify hook\"), hook succeeds: eve credited 100, vault holds 200",
    txs := [(.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1)],
    holds := fun w => quiescent w && w.app.ledger.get .eve == 100 && w.app.ft.get .eve == 0 &&
                      w.app.ft.get .vault == 200 }

/-- Withdraw pays out real tokens. -/
def goalWithdrawPays : Goal :=
  { name := "withdraw pays out: alice receives 100 tokens, her ledger goes to 0",
    txs := [(.alice, .vault, .withdraw 100, 0)],
    holds := fun w => quiescent w && w.app.ft.get .alice == 100 && w.app.ledger.get .alice == 0 }

def goals : List Goal := [goalDepositCredited, goalWithdrawPays]

def defaultScenario : List String :=
  [ "actors:     alice (user), eve (attacker, owns hook), token (NEP-141), vault, hook",
    "amounts:    alice has 100 credited in the vault; eve holds 100 tokens; vault holds 100" ]

def accountingText : List String :=
  [ "solvency (Σ ledger ≤ tokens held by vault, in every state) and",
    "no stuck funds (tokens held ≤ Σ ledger whenever nothing is in flight)" ]

structure Model where
  name : String
  pattern : String
  summary : String
  cfg : Config := {}
  adv : Adversary
  /-- `true` if we expect the explorer to find a violation -/
  vulnerable : Bool
  /-- name of the committed proof that covers this model, if any -/
  proof : Option String := none
  /-- custom contract code (user models); `none` = the vault configured by `cfg` -/
  custom : Option (System (St Acct) Acct (Call Acct)) := none
  /-- custom code with no forced failures, for the liveness search -/
  customHonest : Option (System (St Acct) Acct (Call Acct)) := none
  /-- Lean constant holding this model, and the module defining it (for generated witnesses) -/
  leanName : String
  leanModule : String := "Verifier.Models.Registry"
  /-- Lean name of the initial state (used in `prove` statements) -/
  initLean : String := "NearAsync.Vault.init"
  init : W := Vault.init
  menu : List TxT := Vault.menu
  prop : W → Bool := accounting
  propText : List String := accountingText
  scenario : List String := defaultScenario
  goals : List Goal := Vault.goals
  /-- the no-stuck-funds theorem applies (adversary fails only non-callback receipts) -/
  noStuck : Bool := false
  /-- run the sandbox replay export (only for the six vault models with a Rust counterpart) -/
  sandbox : Bool := true
  /-- this model reconstructs a published incident; shown prominently -/
  disclaimer : Option String := none

def Model.sys (m : Model) : System (St Acct) Acct (Call Acct) := m.custom.getD (system m.cfg m.adv)
def Model.honestSys (m : Model) : System (St Acct) Acct (Call Acct) := m.customHonest.getD (system m.cfg .none)

def m_deposit_vulnerable : Model :=
  { name := "deposit-vulnerable", pattern := "ghost funds (notify failure)",
    summary := "credits the ledger in ft_on_transfer, then returns the notification promise",
    cfg := { depositFixed := false }, adv := .attackerCode, vulnerable := true,
    leanName := "NearAsync.Vault.m_deposit_vulnerable" }

def m_deposit_fixed : Model :=
  { name := "deposit-fixed", pattern := "ghost funds (notify failure)",
    summary := "credits only in the after_notify callback, when the notification succeeded",
    adv := .attackerCode, vulnerable := false,
    proof := some "NearAsync.Vault.Proof.concrete_fixed_solvent",
    leanName := "NearAsync.Vault.m_deposit_fixed" }

def m_noreturn_vulnerable : Model :=
  { name := "noreturn-vulnerable", pattern := "ghost funds (hook returns nothing)",
    summary := "same vulnerable vault; the hook succeeds but returns no value",
    cfg := { depositFixed := false, hookReturns := .unit }, adv := .none, vulnerable := true,
    leanName := "NearAsync.Vault.m_noreturn_vulnerable" }

def m_noreturn_fixed : Model :=
  { name := "noreturn-fixed", pattern := "ghost funds (hook returns nothing)",
    summary := "fixed vault with the same hook that returns no value",
    cfg := { hookReturns := .unit }, adv := .none, vulnerable := false,
    proof := some "NearAsync.Vault.Proof.concrete_fixed_solvent + concrete_no_stuck", noStuck := true,
    leanName := "NearAsync.Vault.m_noreturn_fixed" }

def m_withdraw_vulnerable : Model :=
  { name := "withdraw-vulnerable", pattern := "withdraw without restore",
    summary := "debits the ledger, calls ft_transfer, never restores the ledger if it fails",
    cfg := { withdrawFixed := false }, adv := .nonCallback, vulnerable := true,
    leanName := "NearAsync.Vault.m_withdraw_vulnerable" }

def m_withdraw_fixed : Model :=
  { name := "withdraw-fixed", pattern := "withdraw without restore",
    summary := "restores the ledger in after_withdraw when ft_transfer failed",
    adv := .nonCallback, vulnerable := false,
    proof := some "NearAsync.Vault.Proof.concrete_fixed_solvent + concrete_no_stuck", noStuck := true,
    leanName := "NearAsync.Vault.m_withdraw_fixed" }

/-! ## Minimal model of the 2026 NEAR Intents incident mechanism

NOT their contract. A minimal model, written from scratch, of the mechanism described in the
NEAR Intents postmortem (Oct 16, 2026): a deposit notifies a contract named by the depositor; the
attacker's contract fails the notification on purpose; the token refunds the deposit while the
ledger keeps the credit; the unbacked balance is then withdrawn as real tokens from the pool. -/

def incidentInit : W :=
  { app := { ft := [(.alice, 0), (.eve, 100), (.vault, 300)], ledger := [(.alice, 300)] },
    near := [(.alice, 10), (.eve, 10), (.vault, 10)],
    pending := [], results := [], nextId := 0 }

def incidentMenu : List TxT :=
  [ (.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1),
    (.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1),
    (.eve, .vault, .withdraw 100, 0),
    (.alice, .vault, .withdraw 300, 0) ]

/-- The attacker cannot cash out more than she put in, and the pool stays backed. -/
def noProfit (w : W) : Bool := decide (w.app.ft.get .eve ≤ 100)

def incidentScenario : List String :=
  [ "actors:     alice (the other depositors, pooled), eve (attacker, owns the notified contract), token, vault (the deposit ledger), hook",
    "amounts:    depositors have 300 credited and the vault holds 300; eve holds 100 tokens" ]

def incidentGoals : List Goal :=
  [ { name := "honest deposit with a notification is credited: eve credited 100, vault holds 400",
      txs := [(.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1)],
      holds := fun w => quiescent w && w.app.ledger.get .eve == 100 && w.app.ft.get .vault == 400 },
    { name := "depositors can withdraw: alice receives 300 tokens",
      txs := [(.alice, .vault, .withdraw 300, 0)],
      holds := fun w => quiescent w && w.app.ft.get .alice == 300 && w.app.ledger.get .alice == 0 } ]

def incidentDisclaimer : String :=
  "a minimal model of the mechanism in the NEAR Intents postmortem (Oct 2026), written from scratch — NOT their contract"

def m_incident : Model :=
  { name := "incident-2026-10", pattern := "Oct 2026 NEAR Intents mechanism (minimal model)",
    summary := "credits on deposit, notifies a depositor-chosen contract, returns its promise to the token",
    cfg := { depositFixed := false }, adv := .attackerCode, vulnerable := true,
    leanName := "NearAsync.Vault.m_incident", initLean := "NearAsync.Vault.incidentInit",
    init := incidentInit, menu := incidentMenu, prop := noProfit,
    propText := ["attacker cannot cash out more than she put in (eve's tokens ≤ 100)"],
    scenario := incidentScenario, goals := incidentGoals, sandbox := false,
    disclaimer := some incidentDisclaimer }

def m_incident_fixed : Model :=
  { name := "incident-2026-10-fixed", pattern := "Oct 2026 NEAR Intents mechanism (minimal model), fixed",
    summary := "credits only after the notification succeeded (in the callback); otherwise reports all unused",
    adv := .attackerCode, vulnerable := false,
    proof := some "NearAsync.Vault.Proof.concrete_fixed_solvent_from",
    leanName := "NearAsync.Vault.m_incident_fixed", initLean := "NearAsync.Vault.incidentInit",
    init := incidentInit, menu := incidentMenu, prop := fun w => noProfit w && accounting w,
    propText := ["attacker cannot cash out more than she put in (eve's tokens ≤ 100), and"] ++ accountingText,
    scenario := incidentScenario, goals := incidentGoals, sandbox := false,
    disclaimer := some incidentDisclaimer }

def models : List Model :=
  [ m_incident, m_incident_fixed,
    m_deposit_vulnerable, m_deposit_fixed, m_noreturn_vulnerable, m_noreturn_fixed,
    m_withdraw_vulnerable, m_withdraw_fixed ]

end NearAsync.Vault
