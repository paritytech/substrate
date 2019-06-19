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

use super::{
	AliveContractInfo, BalanceOf, CodeHash, ContractInfo, ContractInfoOf, Module, Trait, TrieId,
	TrieIdGenerator,
};
use crate::exec::StorageKey;
use rstd::cell::RefCell;
use rstd::collections::btree_map::{BTreeMap, Entry};
use rstd::prelude::*;
use runtime_io::blake2_256;
use runtime_primitives::traits::{Bounded, Zero};
use srml_support::traits::{Currency, Imbalance, SignedImbalance, UpdateBalanceOutcome};
use srml_support::{storage::child, StorageMap};
use system;

// Note: we don't provide Option<Contract> because we can't create
// the trie_id in the overlay, thus we provide an overlay on the fields
// specifically.
pub struct ChangeEntry<T: Trait> {
	balance: Option<BalanceOf<T>>,
	/// If None, the code_hash remains untouched.
	code_hash: Option<CodeHash<T>>,
	rent_allowance: Option<BalanceOf<T>>,
	storage: BTreeMap<StorageKey, Option<Vec<u8>>>,
}

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T: Trait> Default for ChangeEntry<T> {
	fn default() -> Self {
		ChangeEntry {
			rent_allowance: Default::default(),
			balance: Default::default(),
			code_hash: Default::default(),
			storage: Default::default(),
		}
	}
}

pub type ChangeSet<T> = BTreeMap<<T as system::Trait>::AccountId, ChangeEntry<T>>;

pub trait AccountDb<T: Trait> {
	/// Account is used when overlayed otherwise trie_id must be provided.
	/// This is for performance reason.
	///
	/// Trie id is None iff account doesn't have an associated trie id in <ContractInfoOf<T>>.
	/// Because DirectAccountDb bypass the lookup for this association.
	fn get_storage(&self, account: &T::AccountId, trie_id: Option<&TrieId>, location: &StorageKey) -> Option<Vec<u8>>;
	/// If account has an alive contract then return the code hash associated.
	fn get_code_hash(&self, account: &T::AccountId) -> Option<CodeHash<T>>;
	/// If account has an alive contract then return the rent allowance associated.
	fn get_rent_allowance(&self, account: &T::AccountId) -> Option<BalanceOf<T>>;
	/// Returns false iff account has no alive contract nor tombstone.
	fn contract_exists(&self, account: &T::AccountId) -> bool;
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T>;

	fn commit(&mut self, change_set: ChangeSet<T>);
}

pub struct DirectAccountDb;
impl<T: Trait> AccountDb<T> for DirectAccountDb {
	fn get_storage(
		&self,
		_account: &T::AccountId,
		trie_id: Option<&TrieId>,
		location: &StorageKey
	) -> Option<Vec<u8>> {
		trie_id.and_then(|id| child::get_raw(id, &blake2_256(location)))
	}
	fn get_code_hash(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.code_hash))
	}
	fn get_rent_allowance(&self, account: &T::AccountId) -> Option<BalanceOf<T>> {
		<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.rent_allowance))
	}
	fn contract_exists(&self, account: &T::AccountId) -> bool {
		<ContractInfoOf<T>>::exists(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T> {
		T::Currency::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		let mut total_imbalance = SignedImbalance::zero();
		for (address, changed) in s.into_iter() {
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

			if changed.code_hash.is_some()
				|| changed.rent_allowance.is_some()
				|| !changed.storage.is_empty()
			{
				let old_info = match <ContractInfoOf<T>>::get(&address) {
					Some(ContractInfo::Alive(alive)) => Some(alive),
					None => None,
					// Cannot commit changes to tombstone contract
					Some(ContractInfo::Tombstone(_)) => continue,
				};

				let mut new_info = if let Some(info) = old_info.clone() {
					info
				} else if let Some(code_hash) = changed.code_hash {
					AliveContractInfo::<T> {
						code_hash,
						storage_size: <Module<T>>::storage_size_offset(),
						trie_id: <T as Trait>::TrieIdGenerator::trie_id(&address),
						deduct_block: <system::Module<T>>::block_number(),
						rent_allowance: <BalanceOf<T>>::max_value(),
						last_write: None,
					}
				} else {
					// No contract exist and no code_hash provided
					continue;
				};

				if let Some(rent_allowance) = changed.rent_allowance {
					new_info.rent_allowance = rent_allowance;
				}

				if let Some(code_hash) = changed.code_hash {
					new_info.code_hash = code_hash;
				}

				if !changed.storage.is_empty() {
					new_info.last_write = Some(<system::Module<T>>::block_number());
				}

				for (k, v) in changed.storage.into_iter() {
					if let Some(value) = child::get_raw(&new_info.trie_id[..], &blake2_256(&k)) {
						new_info.storage_size -= value.len() as u32;
					}
					if let Some(value) = v {
						new_info.storage_size += value.len() as u32;
						child::put_raw(&new_info.trie_id[..], &blake2_256(&k), &value[..]);
					} else {
						child::kill(&new_info.trie_id[..], &blake2_256(&k));
					}
				}

				if old_info
					.map(|old_info| old_info != new_info)
					.unwrap_or(true)
				{
					<ContractInfoOf<T>>::insert(&address, ContractInfo::Alive(new_info));
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
	underlying: &'a dyn AccountDb<T>,
}
impl<'a, T: Trait> OverlayAccountDb<'a, T> {
	pub fn new(underlying: &'a dyn AccountDb<T>) -> OverlayAccountDb<'a, T> {
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
		location: StorageKey,
		value: Option<Vec<u8>>,
	) {
		self.local.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.storage
			.insert(location, value);
	}

	/// Return an error if contract already exists (either if it is alive or tombstone)
	pub fn create_contract(
		&mut self,
		account: &T::AccountId,
		code_hash: CodeHash<T>,
	) -> Result<(), &'static str> {
		if self.contract_exists(account) {
			return Err("Alive contract or tombstone already exists");
		}

		let mut local = self.local.borrow_mut();
		let contract = local.entry(account.clone()).or_insert_with(|| Default::default());

		contract.code_hash = Some(code_hash);
		contract.rent_allowance = Some(<BalanceOf<T>>::max_value());

		Ok(())
	}
	/// Assume contract exists
	pub fn set_rent_allowance(&mut self, account: &T::AccountId, rent_allowance: BalanceOf<T>) {
		self.local
			.borrow_mut()
			.entry(account.clone())
			.or_insert(Default::default())
			.rent_allowance = Some(rent_allowance);
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
	fn get_storage(
		&self,
		account: &T::AccountId,
		trie_id: Option<&TrieId>,
		location: &StorageKey
	) -> Option<Vec<u8>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|a| a.storage.get(location))
			.cloned()
			.unwrap_or_else(|| self.underlying.get_storage(account, trie_id, location))
	}
	fn get_code_hash(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.code_hash)
			.or_else(|| self.underlying.get_code_hash(account))
	}
	fn get_rent_allowance(&self, account: &T::AccountId) -> Option<BalanceOf<T>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.rent_allowance)
			.or_else(|| self.underlying.get_rent_allowance(account))
	}
	fn contract_exists(&self, account: &T::AccountId) -> bool {
		self.local
			.borrow()
			.get(account)
			.map(|a| a.code_hash.is_some())
			.unwrap_or_else(|| self.underlying.contract_exists(account))
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
					value.balance = changed.balance.or(value.balance);
					value.code_hash = changed.code_hash.or(value.code_hash);
					value.rent_allowance = changed.rent_allowance.or(value.rent_allowance);
					value.storage.extend(changed.storage.into_iter());
				}
				Entry::Vacant(e) => {
					e.insert(changed);
				}
			}
		}
	}
}
