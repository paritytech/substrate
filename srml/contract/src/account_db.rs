// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

//! Auxilliaries to help with managing partial changes to accounts state.

use super::{CodeHash, CodeHashOf, StorageOf, Trait};
use {balances, system};
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::prelude::*;
use srml_support::{StorageMap, StorageDoubleMap, traits::UpdateBalanceOutcome};

pub struct ChangeEntry<T: Trait> {
	balance: Option<T::Balance>,
	/// In the case the outer option is None, the code_hash remains untouched, while providing `Some(None)` signifies a removing of the code in question
	code: Option<Option<CodeHash<T>>>,
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

pub type ChangeSet<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

pub trait AccountDb<T: Trait> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;

	fn commit(&mut self, change_set: ChangeSet<T>);
}

pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		<StorageOf<T>>::get(account.clone(), location.to_vec())
	}
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<CodeHashOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		balances::Module::<T>::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				if let UpdateBalanceOutcome::AccountKilled =
					balances::Module::<T>::set_free_balance_creating(&address, balance)
				{
					// Account killed. This will ultimately lead to calling `OnFreeBalanceZero` callback
					// which will make removal of CodeHashOf and StorageOf for this account.
					// In order to avoid writing over the deleted properties we `continue` here.
					continue;
				}
			}
			if let Some(code) = changed.code {
				if let Some(code) = code {
					<CodeHashOf<T>>::insert(&address, code);
				} else {
					<CodeHashOf<T>>::remove(&address);
				}
			}
			for (k, v) in changed.storage.into_iter() {
				if let Some(value) = v {
					<StorageOf<T>>::insert(address.clone(), k, value);
				} else {
					<StorageOf<T>>::remove(address.clone(), k);
				}
			}
		}
	}
}

pub struct OverlayAccountDb<'a, T: Trait + 'a> {
	local: RefCell<ChangeSet<T>>,
	underlying: &'a AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(underlying: &'a AccountDb<T>) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			local: RefCell::new(ChangeSet::new()),
			underlying,
		}
	}

	pub fn into_change_set(self) -> ChangeSet<T> {
		self.local.into_inner()
	}

	pub fn set_storage(
		&mut self,
		account: &T::AccountId,
		location: Vec<u8>,
		value: Option<Vec<u8>>,
	) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.storage
			.insert(location, value);
	}
	pub fn set_code(&mut self, account: &T::AccountId, code: Option<CodeHash<T>>) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.code = Some(code);
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
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
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
	fn commit(&mut self, s: ChangeSet<T>) {
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
