import Verifier.Token

/-!
# Deposit-ledger vault: vulnerable and fixed

A vault accepts NEP-141 deposits through `ft_transfer_call` and keeps an internal ledger.
With `msg = notify hook` it also notifies a third-party contract about the deposit.

* **Vulnerable** (`ghost-funds` pattern): `ft_on_transfer` credits the ledger first, then returns the
  notification promise. If the notification fails, the promise chain fails, so the token's
  `ft_resolve_transfer` refunds the full amount to the sender — but the ledger credit stays.
* **Fixed**: credit only in the callback `after_notify`, and only when the notification succeeded;
  on failure report the whole amount as unused (the token refunds, nothing was credited).

Both versions check that `ft_on_transfer` comes from the token, and offer `withdraw`, which debits
the ledger, sends tokens with `ft_transfer`, and restores the ledger if that transfer fails.
-/

namespace NearAsync.Deposit

open NearAsync

inductive Acct where
  | alice | eve | token | vault | hook
  deriving DecidableEq, Repr

def Acct.name : Acct → String
  | .alice => "alice" | .eve => "eve" | .token => "token" | .vault => "vault" | .hook => "hook"

instance : ToString Acct := ⟨Acct.name⟩

/-- On-chain state of the two contracts we care about. -/
structure St where
  /-- token contract: NEP-141 balances -/
  ft : Bal Acct
  /-- vault contract: internal ledger -/
  ledger : Bal Acct

inductive Version where
  | vulnerable | fixed
  deriving DecidableEq, Repr

/-- The vault's methods. -/
def vaultHandle (v : Version) (ctx : Ctx Acct) (c : Call Acct) (s : St) :
    Outcome St Acct (Call Acct) :=
  match c with
  | .ft_on_transfer sender amt msg =>
    if ctx.pred ≠ .token then .panic "only the token may call ft_on_transfer" else
    match v, msg with
    | _, .plain =>
      .ok { s with ledger := s.ledger.add sender amt } [] (.val (.nat 0))
    | .vulnerable, .notify h =>
      -- BUG: credit now, then return the notification promise. If it fails, the token refunds.
      .ok { s with ledger := s.ledger.add sender amt }
        [ { recv := h, call := .on_deposit sender amt } ] (.promise 0)
    | .fixed, .notify h =>
      .ok s
        [ { recv := h, call := .on_deposit sender amt },
          { recv := ctx.self, call := .after_notify sender amt, after := some 0 } ] (.promise 1)
  | .after_notify who amt =>
    if ctx.pred ≠ ctx.self then .panic "private method" else
    match ctx.input with
    | some (.ok _) => .ok { s with ledger := s.ledger.add who amt } [] (.val (.nat 0))
    | some .failed => .ok s [] (.val (.nat amt))   -- all unused: token refunds, nothing credited
    | none => .panic "no promise result"
  | .withdraw amt =>
    if amt = 0 then .panic "amount must be positive" else
    if s.ledger.get ctx.pred < amt then .panic "insufficient ledger balance" else
    .ok { s with ledger := s.ledger.sub ctx.pred amt }
      [ { recv := .token, call := .ft_transfer ctx.pred amt, deposit := 1 },
        { recv := ctx.self, call := .after_withdraw ctx.pred amt, after := some 0 } ]
      (.val .unit)
  | .after_withdraw who amt =>
    if ctx.pred ≠ ctx.self then .panic "private method" else
    match ctx.input with
    | some (.ok _) => .ok s [] (.val .unit)
    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val .unit)
    | none => .panic "no promise result"
  | _ => .panic "method not found"

/-- A third-party contract that accepts notifications (its owner can make it fail).
It returns `"0"` ("nothing unused"), the value a well-behaved hook would forward. (If it returned
nothing, the token could not parse the result and would refund in full even without a failure —
the explorer finds that variant too.) -/
def hookHandle (ctx : Ctx Acct) (c : Call Acct) (s : St) : Outcome St Acct (Call Acct) :=
  match c with
  | .on_deposit _ _ => .ok s [] (.val (.nat 0))
  | _ => let _ := ctx; .panic "method not found"

/-- Who runs which code. `alice` and `eve` are plain accounts without contracts. -/
def dispatch (v : Version) : Acct → Ctx Acct → Call Acct → St → Outcome St Acct (Call Acct)
  | .token => ftHandle St.ft (fun s ft => { s with ft := ft })
  | .vault => vaultHandle v
  | .hook  => hookHandle
  | _      => fun _ _ _ => .panic "account has no contract"

/-- Adversary models. -/
inductive Adversary where
  /-- Only receipts executing attacker-controlled code (`hook`, owned by eve) may fail. -/
  | attackerCode
  /-- Any function-call receipt may fail (e.g. attacker picks too little gas). Strongest. -/
  | anyReceipt
  deriving DecidableEq, Repr

def canFail : Adversary → Receipt Acct (Call Acct) → Bool
  | .attackerCode, r => decide (r.recv = .hook)
  | .anyReceipt, _ => true

def system (v : Version) (adv : Adversary) : System St Acct (Call Acct) :=
  { dispatch := dispatch v, canFail := canFail adv }

/-! ## Invariant -/

/-- Solvency: the vault's internal ledger is fully backed by tokens it actually holds. -/
def solvent (w : World St Acct (Call Acct)) : Bool :=
  decide (w.app.ledger.total ≤ w.app.ft.get .vault)

/-! ## Scenario: a live vault where alice has already deposited 100 -/

def init : World St Acct (Call Acct) :=
  { app := { ft := [(.alice, 0), (.eve, 100), (.vault, 100)], ledger := [(.alice, 100)] },
    near := [(.alice, 10), (.eve, 10), (.vault, 10)],
    pending := [], results := [], nextId := 0 }

/-- Transactions the actors may send (each at most once in one exploration). -/
def menu : List (Acct × Acct × Call Acct × Nat) :=
  [ (.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1),
    (.eve, .token, .ft_transfer_call .vault 100 .plain, 1),
    (.eve, .vault, .withdraw 100, 0),
    (.alice, .vault, .withdraw 100, 0) ]

end NearAsync.Deposit
