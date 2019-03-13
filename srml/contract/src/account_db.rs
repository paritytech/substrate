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

use super::{CodeHash, CodeHashOf, Trait, SubTrie};
use {balances, system};
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::prelude::*;
use srml_support::{StorageMap, traits::UpdateBalanceOutcome, storage::child};
use substrate_primitives::storage::well_known_keys;

pub struct ChangeEntry<T: Trait> {
	balance: Option<T::Balance>,
	/// In the case the outer option is None, the code_hash remains untouched, while providing `Some(None)` signifies a removing of the code in question
	code: Option<Option<CodeHash<T>>>,
  storage_key_space: Vec<u8>,
	storage: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
}

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T: Trait> Default for ChangeEntry<T> {
	fn default() -> Self {
		ChangeEntry {
			balance: Default::default(),
			code: Default::default(),
      storage_key_space: Default::default(),
			storage: Default::default(),
		}
	}
}

pub type ChangeSet<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

pub trait AccountDb<T: Trait> {
/*	fn get_subtrie<'a>(
    &self,
    key_space: &[u8],
    account: &T::AccountId,
    subtries: &'a mut SubtriesCache<<T as system::Trait>::Hash>)
    -> Option<&'a SubTrie<<T as system::Trait>::Hash>>;*/
	fn get_subtrie(&self, parent_key_space: &[u8], account: &T::AccountId) -> Option<SubTrie>;
	fn get_storage(&self, key_space: &[u8], location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;

	fn commit(&mut self, change_set: ChangeSet<T>);
}


/*
// TODO move this cache in externality with a subtrie struct with more content (aka root & other)
pub struct SubtriesCache<H> {
	// TODO switch to lru ??
	cache: BTreeMap<Vec<u8>, BTreeMap<Vec<u8>, Option<SubTrie<H>>>>,
}
impl<H> SubtriesCache<H> {
	pub fn new() -> Self {
		SubtriesCache{ cache: BTreeMap::new() }
	}
	pub fn get(&self, parent_key_space: &[u8], account_key: &[u8]) -> Option<&Option<SubTrie<H>>> {
		self.cache.get(parent_key_space).and_then(|r|r.get(account_key))
	}
	pub fn entry(&mut self, parent_key_space: Vec<u8>, account_key: Vec<u8>) -> Entry<Vec<u8>, Option<SubTrie<H>>> {
		self.cache.entry(parent_key_space)
			.or_insert_with(|| BTreeMap::new())
			.entry(account_key)
	}
}
*/
pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_subtrie(&self, key_space: &[u8], account: &T::AccountId) -> Option<SubTrie> {
		use parity_codec::KeyedVec;
		// warn slow to_keyed_vec
		let keyed_account = account.to_keyed_vec(well_known_keys::CHILD_STORAGE_KEY_PREFIX);
    // TODO change child to return reference on cache??
		let res: Option<SubTrie> = child::get(key_space, &keyed_account[..]);
    res
/*		if let Some(res) = subtries.get(key_space, &keyed_account[..]) {
			res.as_ref()
		} else {
			let res: Option<SubTrie<<T as system::Trait>::Hash>> = child::get(key_space, &keyed_account[..]);
			subtries.entry(key_space.to_vec(), keyed_account)
				.or_insert(res).as_ref()
		}*/
	}
	fn get_storage(&self, key_space: &[u8], location: &[u8]) -> Option<Vec<u8>> {
		/*use super::KeySpaceGenerator;
		// same thing here parent to default top empty
		let keyspace = <T as Trait>::KeySpaceGenerator::key_space(account, &[]);// TODO this needs subtrie caching!! -> this is not working as every call is different: value need to be access from parent trie*/
			// TODO get keyspace primitive
		child::get_raw(key_space, location) // TODO make a support trait , does not seems usefull
	}
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<CodeHashOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		balances::Module::<T>::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		for (address, changed) in s.into_iter() {
			let keyspace = changed.storage_key_space;
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
					child::put_raw(&keyspace[..], &k, &value[..]); // TODO move value (ref here is bad) TODO need address to for parent root update??
				} else {
					child::kill(&keyspace[..], &k); // TODO also need address???
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
	fn get_subtrie(&self, key_space: &[u8], account: &T::AccountId) -> Option<SubTrie> {
		self.underlying.get_subtrie(key_space, account)
	}
	fn get_storage(&self, key_space: &[u8], location: &[u8]) -> Option<Vec<u8>> {
    unimplemented!() // TODO changeset over key space
/*		self.local
			.borrow()
			.get(key_space)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(key_space, location))
*/
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
