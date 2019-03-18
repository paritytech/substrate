// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use super::{CodeHash, CodeHashOf, Trait, AccountInfo, KeySpace, AccountInfoOf};
use {balances, system};
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::prelude::*;
use srml_support::{StorageMap, traits::UpdateBalanceOutcome, storage::child};

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

#[derive(Clone, Default)]
pub struct AccountKeySpaceMapping<A: Ord> {
	to_account: BTreeMap<KeySpace, A>,
	to_key: BTreeMap<A, KeySpace>,
}

impl<A: Clone + Ord> AccountKeySpaceMapping<A> {

	pub fn new() -> Self {
		AccountKeySpaceMapping {
			to_account: BTreeMap::new(),
			to_key: BTreeMap::new(),
		}
	}

	pub fn insert(&mut self, account: A, ks: KeySpace) {
		self.to_account.insert(ks.clone(), account.clone());
		self.to_key.insert(account, ks);
	}
	pub fn get_keyspace(&self, account: &A) -> Option<&KeySpace> {
		self.to_key.get(account)
	}
	pub fn get_account(&self, ks: &KeySpace) -> Option<&A> {
		self.to_account.get(ks)
	}

}

pub trait AccountDb<T: Trait> {
	fn get_account_info(&self, account: &T::AccountId) -> Option<AccountInfo>;
	fn get_or_create_keyspace(&self, account: &T::AccountId) -> KeySpace;
	// this function is borderline (impl specific to overlaydb). An alternate
	// design is to use rc internally (instead of optional cache) for 
	// overlaydb. It avoid querying the cache through a recursive call,
	// but make `get_subtrie` and `get_or_create_keyspace` recursive call
	// awkward : multiple query or insert (unless we specify top overlaydb instance).
	fn get_account_from_reg_ks(&self, ks: &KeySpace) -> Option<T::AccountId>;
	fn get_storage(&self, key_space: &KeySpace, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;

	fn commit(&mut self, change_set: ChangeSet<T>);
}

pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_account_info(&self, account: &T::AccountId) -> Option<AccountInfo> {
		let res: Option<AccountInfo> = AccountInfoOf::<T>::get(account);
		res
	}
	fn get_or_create_keyspace(&self, account: &T::AccountId) -> KeySpace {
		use super::KeySpaceGenerator;
		<Self as AccountDb<T>>::get_account_info(self, account)
			.map(|s|s.key_space)
			.unwrap_or_else(||<T as Trait>::KeySpaceGenerator::key_space(account))
	}
	fn get_account_from_reg_ks(&self, _: &KeySpace) -> Option<T::AccountId> {
		// very borderline implementation that consider actual usage of accountdb 
		// this function being kind of helper of get_storage function
		// weak design here (for overlayaccountdb it make sense for top level cache)
		None
	}
	fn get_storage(&self, key_space: &KeySpace, location: &[u8]) -> Option<Vec<u8>> {
		child::get_raw(key_space, location)
	}
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<CodeHashOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		balances::Module::<T>::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		for (address, changed) in s.into_iter() {
			let keyspace = <Self as AccountDb<T>>::get_or_create_keyspace(&self, &address);
			if let Some(balance) = changed.balance {
				if let UpdateBalanceOutcome::AccountKilled =
					balances::Module::<T>::set_free_balance_creating(&address, balance)
				{
					// Account killed. This will ultimately lead to calling `OnFreeBalanceZero` callback
					// which will make removal of CodeHashOf and AccountStorage for this account.
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
					child::put_raw(&keyspace[..], &k, &value[..]);
				} else {
					child::kill(&keyspace[..], &k);
				}
			}
		}
	}
}
pub struct OverlayAccountDb<'a, T: Trait + 'a> {
	local: RefCell<ChangeSet<T>>,
	keyspace_account: Option<RefCell<AccountKeySpaceMapping<<T as system::Trait>::AccountId>>>,
	underlying: &'a AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(underlying: &'a AccountDb<T>, keyspace_account: Option<RefCell<AccountKeySpaceMapping<<T as system::Trait>::AccountId>>>) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			local: RefCell::new(ChangeSet::new()),
			keyspace_account,
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
		self.local.borrow_mut()
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
	fn get_account_info(&self, account: &T::AccountId) -> Option<AccountInfo> {
		let v = self.underlying.get_account_info(account);
		v.as_ref().map(|v|
			self.keyspace_account.as_ref().map(|ka|
				ka.borrow_mut().insert(account.clone(), v.key_space.clone())));
		v
	}
	fn get_or_create_keyspace(&self, account: &T::AccountId) -> KeySpace {
		self.keyspace_account.as_ref()
			.map(|ka| {
				let mut ka_mut = ka.borrow_mut();
				if let Some(v) = ka_mut.get_keyspace(account) {
					v.clone()
				} else {
					let v = self.underlying.get_or_create_keyspace(account);
					ka_mut.insert(account.clone(), v.clone());
					v
				}
			})
			.unwrap_or_else(||self.underlying.get_or_create_keyspace(account))
	}
	fn get_account_from_reg_ks(&self, ks: &KeySpace) -> Option<T::AccountId> {
		self.keyspace_account.as_ref()
			.map(|ka| ka.borrow().get_account(ks).cloned())
			.unwrap_or_else(|| self.underlying.get_account_from_reg_ks(ks))
	}
	fn get_storage(&self, key_space: &KeySpace, location: &[u8]) -> Option<Vec<u8>> {
		self.get_account_from_reg_ks(key_space).and_then(|account| self.local
			.borrow()
			.get(&account)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(key_space, location)))
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
