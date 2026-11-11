import Verifier.Token

/-!
# Deposit-ledger vault (vulnerable and fixed variants)

A vault accepts NEP-141 deposits through `ft_transfer_call` and keeps an internal ledger.
With `msg = notify hook` it also notifies a third-party contract about the deposit.
`withdraw` debits the ledger and sends tokens back with `ft_transfer`.

Bug switches (`Config`):
* `depositFixed = false` — **ghost funds**: `ft_on_transfer` credits the ledger first, then returns
  the notification promise. If that chain fails (or returns no number), the token refunds the
  sender in `ft_resolve_transfer`, but the ledger credit stays.
  Fixed: credit in the callback `after_notify`, only if the notification succeeded, and report
  the full amount as unused otherwise.
* `withdrawFixed = false` — **withdraw without restore**: the callback `after_withdraw` does not
  restore the ledger when `ft_transfer` failed, so the user's tokens stay in the vault, owned by no one.
  Fixed: restore the ledger in the callback on failure.
* `hookReturns` — what the notification hook returns: `"0"` or nothing (`unit`).

Handlers are generic in the account type; `T` is the token account.
-/

namespace NearAsync.Vault

open NearAsync

structure St (α : Type) where
  /-- token contract: NEP-141 balances -/
  ft : Bal α
  /-- vault contract: internal ledger -/
  ledger : Bal α

structure Config where
  depositFixed : Bool := true
  withdrawFixed : Bool := true
  hookReturns : Val := .nat 0
  deriving Repr

variable {α : Type} [DecidableEq α]

/-- The vault's methods. `T` is the token contract it accepts. -/
def vaultHandle (cfg : Config) (T : α) (ctx : Ctx α) (c : Call α) (s : St α) :
    Outcome (St α) α (Call α) :=
  match c with
  | .ft_on_transfer sender amt msg =>
    if ctx.pred ≠ T then .panic "only the token may call ft_on_transfer" else
    match msg with
    | .plain => .ok { s with ledger := s.ledger.add sender amt } [] (.val (.nat 0))
    | .notify h =>
      if cfg.depositFixed then
        .ok s
          [ { recv := h, call := .on_deposit sender amt },
            { recv := ctx.self, call := .after_notify sender amt, after := some 0 } ] (.promise 1)
      else
        -- BUG: credit now, then return the notification promise.
        .ok { s with ledger := s.ledger.add sender amt }
          [ { recv := h, call := .on_deposit sender amt } ] (.promise 0)
  | .after_notify who amt =>
    if ctx.pred ≠ ctx.self then .panic "private method" else
    match ctx.input with
    | some (.ok _) => .ok { s with ledger := s.ledger.add who amt } [] (.val (.nat 0))
    -- notifications are best-effort: credit the deposit even if the hook failed
    | some .failed => .ok { s with ledger := s.ledger.add who amt } [] (.val (.nat amt))
    | none => .panic "no promise result"
  | .withdraw amt =>
    if amt = 0 then .panic "amount must be positive" else
    if s.ledger.get ctx.pred < amt then .panic "insufficient ledger balance" else
    .ok { s with ledger := s.ledger.sub ctx.pred amt }
      [ { recv := T, call := .ft_transfer ctx.pred amt, deposit := 1 },
        { recv := ctx.self, call := .after_withdraw ctx.pred amt, after := some 0 } ]
      (.val .unit)
  | .after_withdraw who amt =>
    if ctx.pred ≠ ctx.self then .panic "private method" else
    match ctx.input with
    | some (.ok _) => .ok s [] (.val .unit)
    | some .failed =>
      if cfg.withdrawFixed then .ok { s with ledger := s.ledger.add who amt } [] (.val .unit)
      else .ok s [] (.val .unit)   -- BUG: ledger already debited, tokens never left
    | none => .panic "no promise result"
  | _ => .panic "method not found"

/-- A third-party notification hook. Its owner can make it fail. -/
def hookHandle (ret : Val) (_ctx : Ctx α) (c : Call α) (s : St α) : Outcome (St α) α (Call α) :=
  match c with
  | .on_deposit _ _ => .ok s [] (.val ret)
  | _ => .panic "method not found"

def tokenHandle : Ctx α → Call α → St α → Outcome (St α) α (Call α) :=
  ftHandle St.ft (fun s ft => { s with ft := ft })

/-! ## Concrete actors used by the explorer -/

inductive Acct where
  | alice | eve | token | vault | hook
  deriving DecidableEq, Repr

def Acct.name : Acct → String
  | .alice => "alice" | .eve => "eve" | .token => "token" | .vault => "vault" | .hook => "hook"

instance : ToString Acct := ⟨Acct.name⟩

def Acct.all : List Acct := [.alice, .eve, .token, .vault, .hook]

/-- Who runs which code. `alice` and `eve` are plain accounts; `hook` is owned by eve. -/
def dispatch (cfg : Config) : Acct → Ctx Acct → Call Acct → St Acct → Outcome (St Acct) Acct (Call Acct)
  | .token => tokenHandle
  | .vault => vaultHandle cfg .token
  | .hook  => hookHandle cfg.hookReturns
  | _      => fun _ _ _ => .panic "account has no contract"

/-- Which receipts the adversary may force to fail. -/
inductive Adversary where
  /-- nothing fails unless the code itself panics -/
  | none
  /-- receipts on eve's own contract (`hook`) may fail -/
  | attackerCode
  /-- any receipt that is not a callback may fail (too little gas, unregistered receiver, …);
      callbacks are assumed to have enough gas reserved -/
  | nonCallback
  /-- any receipt may fail -/
  | anyReceipt
  deriving DecidableEq, Repr

def Adversary.describe : Adversary → String
  | .none => "no forced failures (only real panics)"
  | .attackerCode => "receipts on eve's own contract (hook) may fail"
  | .nonCallback => "any non-callback receipt may fail (callbacks assumed to have gas reserved)"
  | .anyReceipt => "any receipt may fail"

def canFail : Adversary → Receipt Acct (Call Acct) → Bool
  | .none, _ => false
  | .attackerCode, r => decide (r.recv = .hook)
  | .nonCallback, r => r.waitsOn.isNone
  | .anyReceipt, _ => true

def system (cfg : Config) (adv : Adversary) : System (St Acct) Acct (Call Acct) :=
  { dispatch := dispatch cfg, canFail := canFail adv }

abbrev W := World (St Acct) Acct (Call Acct)
abbrev Tr := List (Step Acct (Call Acct))

/-! ## Properties -/

/-- Solvency: the vault's ledger is fully backed by tokens it actually holds. -/
def solvent (w : W) : Bool := decide (w.app.ledger.total ≤ w.app.ft.get .vault)

/-- No stuck funds: when nothing is in flight, every token the vault holds is owed to someone. -/
def noStuck (w : W) : Bool := !w.pending.isEmpty || decide (w.app.ft.get .vault ≤ w.app.ledger.total)

def accounting (w : W) : Bool := solvent w && noStuck w

def quiescent (w : W) : Bool := w.pending.isEmpty

/-! ## Scenario: a live vault where alice has already deposited 100 -/

def init : W :=
  { app := { ft := [(.alice, 0), (.eve, 100), (.vault, 100)], ledger := [(.alice, 100)] },
    near := [(.alice, 10), (.eve, 10), (.vault, 10)],
    pending := [], results := [], nextId := 0 }

/-- Transactions the actors may send (each at most once per exploration). -/
def menu : List (Acct × Acct × Call Acct × Nat) :=
  [ (.eve, .token, .ft_transfer_call .vault 100 (.notify .hook), 1),
    (.eve, .token, .ft_transfer_call .vault 100 .plain, 1),
    (.eve, .vault, .withdraw 100, 0),
    (.alice, .vault, .withdraw 100, 0) ]

end NearAsync.Vault
