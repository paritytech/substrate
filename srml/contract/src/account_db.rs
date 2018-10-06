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

use super::{CodeOf, StorageOf, Trait};
use double_map::StorageDoubleMap;
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::marker::PhantomData;
use rstd::prelude::*;
use runtime_support::StorageMap;
use {balances, system};

#[derive(Clone)]
#[cfg_attr(test, derive(PartialEq))]
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

#[cfg(feature = "bench")]
impl<T: Trait> ChangeEntry<T> {
	pub fn new(
		balance: Option<T::Balance>,
		code: Option<Vec<u8>>,
		storage: BTreeMap<Vec<u8>, Option<Vec<u8>>>,
	) -> ChangeEntry<T> {
		ChangeEntry { balance, code, storage }
	}
}

pub type ChangeSet<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

pub trait AccountDb<T: Trait> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>>;
	fn get_code(&self, account: &T::AccountId) -> Vec<u8>;
	fn get_balance(&self, account: &T::AccountId) -> T::Balance;
}

pub trait CheckpointedAccountDb<T: Trait>: AccountDb<T> {
	fn checkpoint(&mut self);
	fn revert(&mut self);
	fn commit_checkpoint(&mut self);
	fn commit(self);
}

pub struct DirectAccountDb<T>(PhantomData<T>);

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T> Default for DirectAccountDb<T> {
	fn default() -> Self {
		DirectAccountDb(PhantomData)
	}
}

impl<T: Trait> AccountDb<T> for DirectAccountDb<T> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		<StorageOf<T>>::get(account.clone(), location.to_vec())
	}

	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		<CodeOf<T>>::get(account)
	}

	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		balances::Module::<T>::free_balance(account)
	}
}

impl<T: Trait> DirectAccountDb<T> {
	fn commit(&mut self, s: ChangeSet<T>) {
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance {
				if let balances::UpdateBalanceOutcome::AccountKilled =
					balances::Module::<T>::set_free_balance_creating(&address, balance)
				{
					// Account killed. This will ultimately lead to calling `OnFreeBalanceZero` callback
					// which will make removal of CodeOf and StorageOf for this account.
					// In order to avoid writing over the deleted properties we `continue` here.
					continue;
				}
			}
			if let Some(code) = changed.code {
				<CodeOf<T>>::insert(&address, &code);
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

pub type CheckpointChangeSet<T> = BTreeMap<<T as system::Trait>::AccountId, Option<ChangeEntry<T>>>;

/// The `OverlayAccountDb` wraps a `DirectAccountDb` and provides functionality for
/// checkpointing, reverting, committing checkpoints (i.e. merging them), and finally
/// committing the existing changes to the underlying `DirectAccountDb`. Creating a new
/// checkpoint implies pushing a new map to a vec that will hold previous state of any
/// written account (only the first write per checkpoint is snapshotted). Reverting a
/// checkpoint is done by popping a map from this vec and reapplying the changes to the
/// current local storage. Checkpoints can also be committed, e.g. after a subcall is
/// successful, so that from that point forward reverting the checkpoint means reverting
/// all changes from both checkpoints. The `OverlayAccountDb` also caches any values
/// fetched from the `DirectAccountDb` in a separate map.
pub struct OverlayAccountDb<'a, T: Trait + 'a> {
	underlying: &'a mut DirectAccountDb<T>,
	cache: RefCell<ChangeSet<T>>,
	local: ChangeSet<T>,
	checkpoints: Vec<CheckpointChangeSet<T>>,
}

impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(underlying: &'a mut DirectAccountDb<T>) -> OverlayAccountDb<'a, T> {
		OverlayAccountDb {
			cache: RefCell::new(ChangeSet::new()),
			local: ChangeSet::new(),
			checkpoints: Vec::new(),
			underlying,
		}
	}

	fn snapshot_and_set<F>(&mut self, account: &T::AccountId, f: F)
		where F: FnOnce(&mut ChangeEntry<T>)
	{
		let checkpoint = self.checkpoints.last_mut();

		match self.local.entry(account.clone()) {
			Entry::Occupied(mut o) => {
				// we only want to checkpoint if we haven't already done so, we
				// only checkpoint the previous on the first write
				checkpoint.map(|c| c.entry(account.clone()).or_insert(Some(o.get().clone())));
				f(o.get_mut());
			},
			Entry::Vacant(v) => {
				// we only want to checkpoint if we haven't already done so, we
				// only checkpoint the previous on the first write
				checkpoint.map(|c| c.entry(account.clone()).or_insert(None));
				f(v.insert(Default::default()));
			},
		}
	}

	pub fn set_storage(
		&mut self,
		account: &T::AccountId,
		location: Vec<u8>,
		value: Option<Vec<u8>>,
	) {
		self.snapshot_and_set(account, |entry| {
			entry.storage.insert(location, value);
		});
	}

	pub fn set_code(&mut self, account: &T::AccountId, code: Vec<u8>) {
		self.snapshot_and_set(account, |entry| {
			entry.code = Some(code);
		});
	}

	pub fn set_balance(&mut self, account: &T::AccountId, balance: T::Balance) {
		self.snapshot_and_set(account, |entry| {
			entry.balance = Some(balance);
		});
	}

	fn get_cache<F, G, V>(&self, account: &T::AccountId, getter: F, setter: G) -> V
	where F: Fn(&ChangeEntry<T>) -> Option<V>,
		  G: Fn(&mut ChangeEntry<T>) -> V
	{
		self.local
			.get(account)
			.and_then(|a| getter(a))
			.or_else(|| {
				self.cache
					.borrow()
					.get(account)
					.and_then(|a| getter(a))
			})
			.unwrap_or_else(|| {
				let mut cache = self.cache.borrow_mut();
				let cache_entry = cache.entry(account.clone())
					.or_insert(Default::default());
				setter(cache_entry)
			})
	}
}

impl<'a, T: Trait> AccountDb<T> for OverlayAccountDb<'a, T> {
	fn get_storage(&self, account: &T::AccountId, location: &[u8]) -> Option<Vec<u8>> {
		self.get_cache(
			account,
			|a| a.storage.get(location).cloned(),
			|cache| {
				let value = self.underlying.get_storage(account, location);
				cache.storage.insert(location.to_vec(), value.clone());
				value
			},
		)
	}

	fn get_code(&self, account: &T::AccountId) -> Vec<u8> {
		self.get_cache(
			account,
			|a| a.code.clone(),
			|cache| {
				let code = self.underlying.get_code(account);
				cache.code = Some(code.clone());
				code
			},
		)
	}

	fn get_balance(&self, account: &T::AccountId) -> T::Balance {
		self.get_cache(
			account,
			|a| a.balance,
			|cache| {
				let balance = self.underlying.get_balance(account);
				cache.balance = Some(balance);
				balance
			},
		)
	}
}

impl<'a, T: Trait> CheckpointedAccountDb<T> for OverlayAccountDb<'a, T> {
	fn checkpoint(&mut self) {
		self.checkpoints.push(CheckpointChangeSet::new());
	}

	fn revert(&mut self) {
		if let Some(checkpoint) = self.checkpoints.pop() {
			for (address, changed) in checkpoint.into_iter() {
				match changed {
					None => self.local.remove(&address),
					Some(entry) => self.local.insert(address, entry),
				};
			}
		}
	}

	fn commit_checkpoint(&mut self) {
		if let Some(checkpoint) = self.checkpoints.pop() {
			if let Some(previous_checkpoint) = self.checkpoints.last_mut() {
				for (address, changed) in checkpoint.into_iter() {
					// we only want to snapshot accounts that were only touched
					// by the latest checkpoint
					previous_checkpoint.entry(address).or_insert(changed);
				}
			}
		}
	}

	fn commit(self) {
		self.underlying.commit(self.local);
	}
}
