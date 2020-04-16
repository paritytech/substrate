// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Auxiliaries to help with managing partial changes to accounts state.

use super::{
	AliveContractInfo, BalanceOf, CodeHash, ContractInfo, ContractInfoOf, Trait, TrieId,
	TrieIdGenerator,
};
use crate::exec::StorageKey;
use sp_std::cell::RefCell;
use sp_std::collections::btree_map::{BTreeMap, Entry};
use sp_std::prelude::*;
use sp_io::hashing::blake2_256;
use sp_runtime::traits::{Bounded, Zero};
use frame_support::traits::{Currency, Get, Imbalance, SignedImbalance};
use frame_support::{storage::child, StorageMap};
use frame_system;

// Note: we don't provide Option<Contract> because we can't create
// the trie_id in the overlay, thus we provide an overlay on the fields
// specifically.
pub struct ChangeEntry<T: Trait> {
	/// If Some(_), then the account balance is modified to the value. If None and `reset` is false,
	/// the balance unmodified. If None and `reset` is true, the balance is reset to 0.
	balance: Option<BalanceOf<T>>,
	/// If Some(_), then a contract is instantiated with the code hash. If None and `reset` is false,
	/// then the contract code is unmodified. If None and `reset` is true, the contract is deleted.
	code_hash: Option<CodeHash<T>>,
	/// If Some(_), then the rent allowance is set to the value. If None and `reset` is false, then
	/// the rent allowance is unmodified. If None and `reset` is true, the contract is deleted.
	rent_allowance: Option<BalanceOf<T>>,
	storage: BTreeMap<StorageKey, Option<Vec<u8>>>,
	/// If true, indicates that the existing contract and all its storage entries should be removed
	/// and replaced with the fields on this change entry. Otherwise, the fields on this change
	/// entry are updates merged into the existing contract info and storage.
	reset: bool,
}

impl<T: Trait> ChangeEntry<T> {
	fn balance(&self) -> Option<BalanceOf<T>> {
		self.balance.or_else(|| {
			if self.reset {
				Some(<BalanceOf<T>>::zero())
			} else {
				None
			}
		})
	}

	fn code_hash(&self) -> Option<Option<CodeHash<T>>> {
		if self.reset {
			Some(self.code_hash)
		} else {
			self.code_hash.map(Some)
		}
	}

	fn rent_allowance(&self) -> Option<Option<BalanceOf<T>>> {
		if self.reset {
			Some(self.rent_allowance)
		} else {
			self.rent_allowance.map(Some)
		}
	}

	fn storage(&self, location: &StorageKey) -> Option<Option<Vec<u8>>> {
		let value = self.storage.get(location).cloned();
		if self.reset {
			Some(value.unwrap_or(None))
		} else {
			value
		}
	}
}

// Cannot derive(Default) since it erroneously bounds T by Default.
impl<T: Trait> Default for ChangeEntry<T> {
	fn default() -> Self {
		ChangeEntry {
			rent_allowance: Default::default(),
			balance: Default::default(),
			code_hash: Default::default(),
			storage: Default::default(),
			reset: false,
		}
	}
}

pub type ChangeSet<T> = BTreeMap<<T as frame_system::Trait>::AccountId, ChangeEntry<T>>;

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
		trie_id.and_then(|id| child::get_raw(&crate::child_trie_info(&id[..]), &blake2_256(location)))
	}
	fn get_code_hash(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.code_hash))
	}
	fn get_rent_allowance(&self, account: &T::AccountId) -> Option<BalanceOf<T>> {
		<ContractInfoOf<T>>::get(account).and_then(|i| i.as_alive().map(|i| i.rent_allowance))
	}
	fn contract_exists(&self, account: &T::AccountId) -> bool {
		<ContractInfoOf<T>>::contains_key(account)
	}
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T> {
		T::Currency::free_balance(account)
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		let mut total_imbalance = SignedImbalance::zero();
		for (address, changed) in s.into_iter() {
			if let Some(balance) = changed.balance() {
				let imbalance = T::Currency::make_free_balance_be(&address, balance);
				total_imbalance = total_imbalance.merge(imbalance);
			}

			if changed.code_hash().is_some()
				|| changed.rent_allowance().is_some()
				|| !changed.storage.is_empty()
				|| changed.reset
			{
				let old_info = match <ContractInfoOf<T>>::get(&address) {
					Some(ContractInfo::Alive(alive)) => Some(alive),
					None => None,
					// Cannot commit changes to tombstone contract
					Some(ContractInfo::Tombstone(_)) => continue,
				};

				let mut new_info = match (changed.reset, old_info.clone(), changed.code_hash) {
					// Existing contract is being modified.
					(false, Some(info), _) => info,
					// Existing contract is being removed.
					(true, Some(info), None) => {
						child::kill_storage(&info.child_trie_info());
						<ContractInfoOf<T>>::remove(&address);
						continue;
					}
					// Existing contract is being replaced by a new one.
					(true, Some(info), Some(code_hash)) => {
						child::kill_storage(&info.child_trie_info());
						AliveContractInfo::<T> {
							code_hash,
							storage_size: T::StorageSizeOffset::get(),
							trie_id: <T as Trait>::TrieIdGenerator::trie_id(&address),
							deduct_block: <frame_system::Module<T>>::block_number(),
							rent_allowance: <BalanceOf<T>>::max_value(),
							last_write: None,
						}
					}
					// New contract is being instantiated.
					(_, None, Some(code_hash)) => {
						AliveContractInfo::<T> {
							code_hash,
							storage_size: T::StorageSizeOffset::get(),
							trie_id: <T as Trait>::TrieIdGenerator::trie_id(&address),
							deduct_block: <frame_system::Module<T>>::block_number(),
							rent_allowance: <BalanceOf<T>>::max_value(),
							last_write: None,
						}
					}
					// There is no existing at the address nor a new one to be instantiated.
					(_, None, None) => continue,
				};

				if let Some(rent_allowance) = changed.rent_allowance {
					new_info.rent_allowance = rent_allowance;
				}

				if let Some(code_hash) = changed.code_hash {
					new_info.code_hash = code_hash;
				}

				if !changed.storage.is_empty() {
					new_info.last_write = Some(<frame_system::Module<T>>::block_number());
				}

				for (k, v) in changed.storage.into_iter() {
					if let Some(value) = child::get_raw(
						&new_info.child_trie_info(),
						&blake2_256(&k),
					) {
						new_info.storage_size -= value.len() as u32;
					}
					if let Some(value) = v {
						new_info.storage_size += value.len() as u32;
						child::put_raw(&new_info.child_trie_info(), &blake2_256(&k), &value[..]);
					} else {
						child::kill(&new_info.child_trie_info(), &blake2_256(&k));
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
	pub fn instantiate_contract(
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

	/// Mark a contract as deleted.
	pub fn destroy_contract(&mut self, account: &T::AccountId) {
		let mut local = self.local.borrow_mut();
		local.insert(
			account.clone(),
			ChangeEntry {
				reset: true,
				..Default::default()
			}
		);
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
			.and_then(|changes| changes.storage(location))
			.unwrap_or_else(|| self.underlying.get_storage(account, trie_id, location))
	}
	fn get_code_hash(&self, account: &T::AccountId) -> Option<CodeHash<T>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.code_hash())
			.unwrap_or_else(|| self.underlying.get_code_hash(account))
	}
	fn get_rent_allowance(&self, account: &T::AccountId) -> Option<BalanceOf<T>> {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.rent_allowance())
			.unwrap_or_else(|| self.underlying.get_rent_allowance(account))
	}
	fn contract_exists(&self, account: &T::AccountId) -> bool {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.code_hash().map(|code_hash| code_hash.is_some()))
			.unwrap_or_else(|| self.underlying.contract_exists(account))
	}
	fn get_balance(&self, account: &T::AccountId) -> BalanceOf<T> {
		self.local
			.borrow()
			.get(account)
			.and_then(|changes| changes.balance())
			.unwrap_or_else(|| self.underlying.get_balance(account))
	}
	fn commit(&mut self, s: ChangeSet<T>) {
		let mut local = self.local.borrow_mut();

		for (address, changed) in s.into_iter() {
			match local.entry(address) {
				Entry::Occupied(e) => {
					let mut value = e.into_mut();
					if changed.reset {
						*value = changed;
					} else {
						value.balance = changed.balance.or(value.balance);
						value.code_hash = changed.code_hash.or(value.code_hash);
						value.rent_allowance = changed.rent_allowance.or(value.rent_allowance);
						value.storage.extend(changed.storage.into_iter());
					}
				}
				Entry::Vacant(e) => {
					e.insert(changed);
				}
			}
		}
	}
}
