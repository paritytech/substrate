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

use super::{CodeHash, CodeHashOf, Trait, AccountInfo, TrieId, AccountInfoOf, BalanceOf};
use system;
use rstd::cell::RefCell;
use rstd::rc::Rc;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::prelude::*;
use runtime_primitives::traits::Zero;
use srml_support::{StorageMap, traits::{UpdateBalanceOutcome,
	SignedImbalance, Currency, Imbalance}, storage::child};

pub struct ChangeEntry<T: Trait> {
	balance: Option<BalanceOf<T>>,
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
pub struct AccountTrieIdMapping<A: Ord> {
	to_account: BTreeMap<TrieId, A>,
	to_key: BTreeMap<A, TrieId>,
	// this lock is related to the way overlaydb stack
	// if set it must be unset at the lower level
	lock: bool,
}

impl<A: Clone + Ord> AccountTrieIdMapping<A> {

	pub fn new() -> Self {
		AccountTrieIdMapping {
			to_account: BTreeMap::new(),
			to_key: BTreeMap::new(),
			lock: false,
		}
	}

	pub fn lock(&mut self) {
		self.lock = true;
	}
	pub fn unlock(&mut self) {
		self.lock = false;
	}
	pub fn insert(&mut self, account: A, ks: TrieId) {
		self.to_account.insert(ks.clone(), account.clone());
		self.to_key.insert(account, ks);
	}
	pub fn get_trieid(&self, account: &A) -> Option<&TrieId> {
		if self.lock { return None }
		self.to_key.get(account)
	}
	pub fn get_account(&self, ks: &TrieId) -> Option<&A> {
		if self.lock { return None }
		self.to_account.get(ks)
	}

}

pub trait AccountDb<T: Trait> {
	fn get_account_info(&self, account: &T::AccountId) -> Option<AccountInfo>;
	fn get_or_create_trieid(&self, account: &T::AccountId) -> TrieId;
	fn get_storage(&self, trie_id: &TrieId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>>;
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T>;

	fn commit(&mut self, change_set: ChangeSet<T>);
}

pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_account_info(&self, account: &T::AccountId) -> Option<AccountInfo> {
		let res: Option<AccountInfo> = AccountInfoOf::<T>::get(account);
		res
	}
	fn get_or_create_trieid(&self, account: &T::AccountId) -> TrieId {
		use super::TrieIdGenerator;
		<Self as AccountDb<T>>::get_account_info(self, account)
			.map(|s|s.trie_id)
			.unwrap_or_else(||<T as Trait>::TrieIdGenerator::trie_id(account))
	}
	fn get_storage(&self, trie_id: &TrieId, location: &[u8]) -> Option<Vec<u8>> {
		child::get_raw(trie_id, location)
	}
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<CodeHashOf<T>>::get(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T> {
		T::Currency::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		let mut total_imbalance = SignedImbalance::zero();
		for (address, changed) in s.into_iter() {
			let trieid = <Self as AccountDb<T>>::get_or_create_trieid(&self, &address);
			if let Some(balance) = changed.balance {
				let (imbalance, outcome) = T::Currency::make_free_balance_be(&address, balance);
				total_imbalance = total_imbalance.merge(imbalance);
				if let UpdateBalanceOutcome::AccountKilled = outcome {
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
					child::put_raw(&trieid[..], &k, &value[..]);
				} else {
					child::kill(&trieid[..], &k);
				}
			}
		}

		match total_imbalance {
			// If we've detected a positive imbalance as a result of our contract-level machinations
			// then it's indicative of a buggy contracts system.
			// Panicking is far from ideal as it opens up a DoS attack on block validators, however
			// it's a less bad option than allowing arbitrary value to be created.
			SignedImbalance::Positive(ref p) if !p.peek().is_zero() =>
				panic!("contract subsystem resulting in positive imbalance!"),
			_ => {}
		}
	}
}
pub struct OverlayAccountDb<'a, T: Trait + 'a> {
	local: RefCell<ChangeSet<T>>,
	trie_account: Rc<RefCell<AccountTrieIdMapping<<T as system::Trait>::AccountId>>>,
	trie_account_cache: bool,
	underlying: &'a AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(
		underlying: &'a AccountDb<T>,
		trie_account: Rc<RefCell<AccountTrieIdMapping<<T as system::Trait>::AccountId>>>,
		trie_account_cache: bool,
	) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			local: RefCell::new(ChangeSet::new()),
			trie_account,
			trie_account_cache,
			underlying,
		}
	}

	pub fn reg_cache_new_rc(&self) -> Rc<RefCell<AccountTrieIdMapping<<T as system::Trait>::AccountId>>> {
		self.trie_account.clone()
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
	pub fn set_balance(&mut self, account: &T::AccountId, balance: BalanceOf<T>) {
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
		if self.trie_account_cache {
			v.as_ref().map(|v|self.trie_account.as_ref().borrow_mut().insert(account.clone(), v.trie_id.clone()));
		}
		v
	}
	fn get_or_create_trieid(&self, account: &T::AccountId) -> TrieId {
		if self.trie_account_cache {
			let mut ka_mut = self.trie_account.as_ref().borrow_mut();
			if let Some(v) = ka_mut.get_trieid(account) {
				v.clone()
			} else {
				ka_mut.unlock();
				let v = self.underlying.get_or_create_trieid(account);
				ka_mut.insert(account.clone(), v.clone());
				v
			}
		} else {
			let res = self.trie_account.as_ref().borrow().get_trieid(account).map(|v|v.clone());
			res.unwrap_or_else(|| {
				self.trie_account.as_ref().borrow_mut().lock();
				self.underlying.get_or_create_trieid(account)
			})
		}
	}
	fn get_storage(&self, ks: &TrieId, location: &[u8]) -> Option<Vec<u8>> {
		self.trie_account.as_ref().borrow().get_account(ks).and_then(|account| self.local
			.borrow()
			.get(&account)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(ks, location)))
	}
	fn get_code(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.code.clone())
			.unwrap_or_else(|| self.underlying.get_code(account))
	}
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T> {
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
