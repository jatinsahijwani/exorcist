//! Notification hook controlled by its owner. Modes:
//! `ok` returns "0", `none` succeeds and returns nothing, `panic` fails.
use near_sdk::json_types::U128;
use near_sdk::{env, log, near, require, AccountId, PanicOnDefault};

#[near(contract_state)]
#[derive(PanicOnDefault)]
pub struct Hook {
    owner: AccountId,
    mode: String,
}

#[near]
impl Hook {
    #[init]
    pub fn new(owner: AccountId, mode: String) -> Self {
        Self { owner, mode }
    }

    pub fn set_mode(&mut self, mode: String) {
        require!(env::predecessor_account_id() == self.owner, "owner only");
        self.mode = mode;
    }

    pub fn mode(&self) -> String {
        self.mode.clone()
    }

    pub fn on_deposit(&mut self, who: AccountId, amount: U128) {
        log!("EXORCIST on_deposit");
        let _ = (who, amount);
        match self.mode.as_str() {
            "ok" => env::value_return(b"\"0\""),
            "none" => {}
            _ => env::panic_str("hook refuses"),
        }
    }
}
