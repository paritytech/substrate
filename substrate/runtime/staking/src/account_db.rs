// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Auxilliaries to help with managing partial changes to accounts state.

use rstd::prelude::*;
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use runtime_support::StorageMap;
use super::*;

pub struct ChangeEntry<T: Trait> {
	balance: Option<T::Balance>,
	code: Option<Vec<u8>>,
	storage: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
}

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T: Trait> Default for ChangeEntry<T> {
	fn default() -> Self {
		ChangeEntry {
			balance: Default::default(),
			code: Default::default(),
			storage: Default::default(),
		}
	}
}

impl<T: Trait> ChangeEntry<T> {
	pub fn contract_created(b: T::Balance, c: Vec<u8>) -> Self {
		ChangeEntry { balance: Some(b), code: Some(c), storage: Default::default() }
	}
	pub fn balance_changed(b: T::Balance) -> Self {
		ChangeEntry { balance: Some(b), code: None, storage: Default::default() }
	}
}

pub type State<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

pub trait AccountDb<T: Trait> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Vec<u8>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;

	fn merge(&mut self, state: State<T>);
}

pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		<StorageOf<T>>::get(&(account.clone(), location.to_vec()))
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		<CodeOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		<FreeBalance<T>>::get(account)
	}
	fn merge(&mut self, s: State<T>) {
		let ed = <Module<T>>::existential_deposit();
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				// If the balance is too low, then the account is reaped.
				// NOTE: There are two balances for every account: `reserved_balance` and
				// `free_balance`. This contract subsystem only cares about the latter: whenever
				// the term "balance" is used *here* it should be assumed to mean "free balance"
				// in the rest of the module.
				// Free balance can never be less than ED. If that happens, it gets reduced to zero
				// and the account information relevant to this subsystem is deleted (i.e. the
				// account is reaped).
				// NOTE: This is orthogonal to the `Bondage` value that an account has, a high
				// value of which makes even the `free_balance` unspendable.
				// TODO: enforce this for the other balance-altering functions.
				if balance < ed {
					<Module<T>>::on_free_too_low(&address);
					continue;
				} else {
					if !<FreeBalance<T>>::exists(&address) {
						let outcome = <Module<T>>::new_account(&address, balance);
						let credit = match outcome {
							NewAccountOutcome::GoodHint => balance + <Module<T>>::reclaim_rebate(),
							_ => balance,
						};
						<FreeBalance<T>>::insert(&address, credit);
					} else {
						<FreeBalance<T>>::insert(&address, balance);
					}
				}
			}
			if let Some(code) = changed.code {
				<CodeOf<T>>::insert(&address, &code);
			}
			for (k, v) in changed.storage.into_iter() {
				if let Some(value) = v {
					<StorageOf<T>>::insert((address.clone(), k), &value);
				} else {
					<StorageOf<T>>::remove((address.clone(), k));
				}
			}
		}
	}
}

pub struct OverlayAccountDb<'a, T: Trait + 'a> {
	local: RefCell<State<T>>,
	underlying: &'a AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(underlying: &'a AccountDb<T>) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			local: RefCell::new(State::new()),
			underlying,
		}
	}

	pub fn into_state(self) -> State<T> {
		self.local.into_inner()
	}

	fn set_storage(&mut self, account: &T::AccountId, location: Vec<u8>, value: Option<Vec<u8>>) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.storage
			.insert(location, value);
	}
	pub fn set_balance(&mut self, account: &T::AccountId, balance: T::Balance) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.balance = Some(balance);
	}
}

impl<'a, T: Trait> AccountDb<T> for OverlayAccountDb<'a, T> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(account, location))
	}
	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.code.clone())
			.unwrap_or_else(|| self.underlying.get_code(account))
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.balance)
			.unwrap_or_else(|| self.underlying.get_balance(account))
	}
	fn merge(&mut self, s: State<T>) {
		let mut local = self.local.borrow_mut();

		for (address, changed) in s.into_iter() {
			match local.entry(address) {
				Entry::Occupied(e) => {
					let mut value = e.into_mut();
					if changed.balance.is_some() {
						value.balance = changed.balance;
					}
					if changed.code.is_some() {
						value.code = changed.code;
					}
					value.storage.extend(changed.storage.into_iter());
				}
				Entry::Vacant(e) => {
					e.insert(changed);
				}
			}
		}
	}
}

pub(crate) struct StakingExt<'a, 'b: 'a, T: Trait + 'b> {
	pub account_db: &'a mut OverlayAccountDb<'b, T>,
	pub account: T::AccountId,
}
impl<'a, 'b: 'a, T: Trait> contract::Ext for StakingExt<'a, 'b, T> {
	type AccountId = T::AccountId;
	type Balance = T::Balance;

	fn get_storage(&self, key: &[u8]) -> Option<Vec<u8>> {
		self.account_db.get_storage(&self.account, key)
	}
	fn set_storage(&mut self, key: &[u8], value: Option<Vec<u8>>) {
		self.account_db.set_storage(&self.account, key.to_vec(), value);
	}
	fn create(&mut self, code: &[u8], value: Self::Balance) {
		if let Ok(Some(commit_state)) =
			Module::<T>::effect_create(&self.account, code, value, self.account_db)
		{
			self.account_db.merge(commit_state);
		}
	}
	fn transfer(&mut self, to: &Self::AccountId, value: Self::Balance) {
		if let Ok(Some(commit_state)) =
			Module::<T>::effect_transfer(&self.account, to, value, self.account_db)
		{
			self.account_db.merge(commit_state);
		}
	}
}
