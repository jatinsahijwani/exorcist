//! Deposit-ledger vault used by Exorcist's sandbox validation.
//!
//! Build features select the variant (mirroring `Verifier/Models/Vault.lean`):
//! * default: fixed vault
//! * `ghost_funds_bug`: credits the ledger in `ft_on_transfer`, then returns the notification promise
//! * `withdraw_no_restore_bug`: never restores the ledger when the payout `ft_transfer` fails
use near_sdk::json_types::U128;
use near_sdk::store::LookupMap;
use near_sdk::{env, ext_contract, log, near, require, AccountId, Gas, NearToken, PanicOnDefault, PromiseOrValue};

const GAS_FOR_HOOK: Gas = Gas::from_tgas(10);
const GAS_FOR_FT_TRANSFER: Gas = Gas::from_tgas(10);
const GAS_FOR_CALLBACK: Gas = Gas::from_tgas(10);

#[ext_contract(ext_hook)]
#[allow(dead_code)]
trait Hook {
    fn on_deposit(&mut self, who: AccountId, amount: U128);
}

#[ext_contract(ext_token)]
#[allow(dead_code)]
trait Token {
    fn ft_transfer(&mut self, receiver_id: AccountId, amount: U128, memo: Option<String>);
}

#[ext_contract(ext_self)]
#[allow(dead_code)]
trait Callbacks {
    fn after_notify(&mut self, who: AccountId, amount: U128) -> U128;
    fn after_withdraw(&mut self, who: AccountId, amount: U128);
}

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Vault {
    token: AccountId,
    ledger: LookupMap<AccountId, u128>,
}

#[near]
impl Vault {
    #[init]
    pub fn new(token: AccountId) -> Self {
        Self { token, ledger: LookupMap::new(b"l") }
    }

    pub fn ledger_of(&self, account_id: AccountId) -> U128 {
        U128(self.ledger.get(&account_id).copied().unwrap_or(0))
    }

    /// NEP-141 receiver. `msg = ""` deposits; `msg = "notify <account>"` also notifies a hook.
    pub fn ft_on_transfer(&mut self, sender_id: AccountId, amount: U128, msg: String) -> PromiseOrValue<U128> {
        log!("EXORCIST ft_on_transfer");
        require!(env::predecessor_account_id() == self.token, "only the token may call ft_on_transfer");
        if msg.is_empty() {
            self.credit(&sender_id, amount.0);
            return PromiseOrValue::Value(U128(0));
        }
        let hook: AccountId = msg
            .strip_prefix("notify ")
            .unwrap_or_else(|| env::panic_str("unknown msg"))
            .parse()
            .unwrap_or_else(|_| env::panic_str("bad hook account"));
        if cfg!(feature = "ghost_funds_bug") {
            // BUG: credit first, then hand the token the notification's result.
            self.credit(&sender_id, amount.0);
            ext_hook::ext(hook).with_static_gas(GAS_FOR_HOOK).on_deposit(sender_id, amount).into()
        } else {
            ext_hook::ext(hook)
                .with_static_gas(GAS_FOR_HOOK)
                .on_deposit(sender_id.clone(), amount)
                .then(ext_self::ext(env::current_account_id()).with_static_gas(GAS_FOR_CALLBACK).after_notify(sender_id, amount))
                .into()
        }
    }

    /// Credit only if the notification succeeded; otherwise report everything as unused.
    #[private]
    pub fn after_notify(&mut self, who: AccountId, amount: U128) -> U128 {
        log!("EXORCIST after_notify");
        if env::promise_result_checked(0, 1024).is_ok() {
            self.credit(&who, amount.0);
            U128(0)
        } else {
            U128(amount.0)
        }
    }

    pub fn withdraw(&mut self, amount: U128) {
        log!("EXORCIST withdraw");
        require!(amount.0 > 0, "amount must be positive");
        let who = env::predecessor_account_id();
        let balance = self.ledger.get(&who).copied().unwrap_or(0);
        require!(balance >= amount.0, "insufficient ledger balance");
        self.ledger.insert(who.clone(), balance - amount.0);
        let _ = ext_token::ext(self.token.clone())
            .with_attached_deposit(NearToken::from_yoctonear(1))
            .with_static_gas(GAS_FOR_FT_TRANSFER)
            .ft_transfer(who.clone(), amount, None)
            .then(ext_self::ext(env::current_account_id()).with_static_gas(GAS_FOR_CALLBACK).after_withdraw(who, amount));
    }

    #[private]
    pub fn after_withdraw(&mut self, who: AccountId, amount: U128) {
        log!("EXORCIST after_withdraw");
        if env::promise_result_checked(0, 1024).is_err() && !cfg!(feature = "withdraw_no_restore_bug") {
            self.credit(&who, amount.0);
        }
    }
}

impl Vault {
    fn credit(&mut self, who: &AccountId, amount: u128) {
        let b = self.ledger.get(who).copied().unwrap_or(0);
        self.ledger.insert(who.clone(), b + amount);
    }
}
