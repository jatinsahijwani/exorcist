//! A minimal NEP-141 fungible token, written for Exorcist's sandbox validation.
//! Semantics follow the NEP-141 reference implementation in near-sdk-rs 5.30.1:
//! 1 yoctoNEAR on transfers, tokens move inside the `ft_transfer_call` receipt, and
//! `ft_resolve_transfer` refunds `min(unused, receiver balance)` where unused is the parsed
//! U128 result, or the full amount if the promise failed or did not return a number.
//! Registration is a simplified NEP-145: `register` / `unregister`.
use near_sdk::json_types::U128;
use near_sdk::store::LookupMap;
use near_sdk::{env, ext_contract, log, near, require, AccountId, Gas, NearToken, PanicOnDefault, PromiseOrValue};

const GAS_FOR_RESOLVE_TRANSFER: Gas = Gas::from_tgas(5);

#[ext_contract(ext_receiver)]
#[allow(dead_code)]
trait Receiver {
    fn ft_on_transfer(&mut self, sender_id: AccountId, amount: U128, msg: String) -> PromiseOrValue<U128>;
}

#[ext_contract(ext_self)]
#[allow(dead_code)]
trait Resolver {
    fn ft_resolve_transfer(&mut self, sender_id: AccountId, receiver_id: AccountId, amount: U128) -> U128;
}

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Token {
    balances: LookupMap<AccountId, u128>,
    total_supply: u128,
}

#[near]
impl Token {
    #[init]
    pub fn new(owner_id: AccountId, total_supply: U128) -> Self {
        let mut balances = LookupMap::new(b"b");
        balances.insert(owner_id, total_supply.0);
        Self { balances, total_supply: total_supply.0 }
    }

    /// Simplified storage registration: any attached deposit is accepted.
    #[payable]
    pub fn register(&mut self, account_id: AccountId) {
        if !self.balances.contains_key(&account_id) {
            self.balances.insert(account_id, 0);
        }
    }

    /// Remove the caller's registration; only with a zero balance.
    #[payable]
    pub fn unregister(&mut self) {
        require!(env::attached_deposit() == NearToken::from_yoctonear(1), "Requires attached deposit of exactly 1 yoctoNEAR");
        let who = env::predecessor_account_id();
        require!(self.balances.get(&who).copied() == Some(0), "balance must be zero to unregister");
        self.balances.remove(&who);
    }

    pub fn ft_balance_of(&self, account_id: AccountId) -> U128 {
        U128(self.balances.get(&account_id).copied().unwrap_or(0))
    }

    pub fn ft_total_supply(&self) -> U128 {
        U128(self.total_supply)
    }

    #[payable]
    pub fn ft_transfer(&mut self, receiver_id: AccountId, amount: U128, memo: Option<String>) {
        log!("EXORCIST ft_transfer");
        let _ = memo;
        require!(env::attached_deposit() == NearToken::from_yoctonear(1), "Requires attached deposit of exactly 1 yoctoNEAR");
        let sender_id = env::predecessor_account_id();
        self.move_tokens(&sender_id, &receiver_id, amount.0);
    }

    #[payable]
    pub fn ft_transfer_call(
        &mut self,
        receiver_id: AccountId,
        amount: U128,
        memo: Option<String>,
        msg: String,
    ) -> PromiseOrValue<U128> {
        log!("EXORCIST ft_transfer_call");
        let _ = memo;
        require!(env::attached_deposit() == NearToken::from_yoctonear(1), "Requires attached deposit of exactly 1 yoctoNEAR");
        let sender_id = env::predecessor_account_id();
        self.move_tokens(&sender_id, &receiver_id, amount.0);
        ext_receiver::ext(receiver_id.clone())
            .with_unused_gas_weight(1)
            .ft_on_transfer(sender_id.clone(), amount, msg)
            .then(
                ext_self::ext(env::current_account_id())
                    .with_static_gas(GAS_FOR_RESOLVE_TRANSFER)
                    .with_unused_gas_weight(0)
                    .ft_resolve_transfer(sender_id, receiver_id, amount),
            )
            .into()
    }

    #[private]
    pub fn ft_resolve_transfer(&mut self, sender_id: AccountId, receiver_id: AccountId, amount: U128) -> U128 {
        log!("EXORCIST ft_resolve_transfer");
        let amount = amount.0;
        let unused = match env::promise_result_checked(0, 64) {
            Ok(bytes) => serde_json::from_slice::<U128>(&bytes).map(|u| u.0).unwrap_or(amount),
            Err(_) => amount,
        }
        .min(amount);
        if unused > 0 {
            let receiver_balance = self.balances.get(&receiver_id).copied().unwrap_or(0);
            if receiver_balance > 0 {
                let refund = receiver_balance.min(unused);
                self.balances.insert(receiver_id, receiver_balance - refund);
                if let Some(sender_balance) = self.balances.get(&sender_id).copied() {
                    self.balances.insert(sender_id, sender_balance + refund);
                    return U128(amount - refund);
                } else {
                    // sender account deleted / unregistered: the refund is burned
                    self.total_supply -= refund;
                    return U128(amount);
                }
            }
        }
        U128(amount)
    }
}

impl Token {
    fn move_tokens(&mut self, sender_id: &AccountId, receiver_id: &AccountId, amount: u128) {
        require!(sender_id != receiver_id, "Sender and receiver should be different");
        require!(amount > 0, "The amount should be a positive number");
        let sb = *self.balances.get(sender_id).unwrap_or_else(|| env::panic_str(&format!("The account {} is not registered", sender_id)));
        require!(sb >= amount, "The account doesn't have enough balance");
        let rb = *self.balances.get(receiver_id).unwrap_or_else(|| env::panic_str(&format!("The account {} is not registered", receiver_id)));
        self.balances.insert(sender_id.clone(), sb - amount);
        self.balances.insert(receiver_id.clone(), rb + amount);
    }
}
