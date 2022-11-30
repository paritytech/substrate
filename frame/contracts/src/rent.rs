// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A module responsible for computing the right amount of weight and charging it.

use crate::{
	AliveContractInfo, BalanceOf, ContractInfo, ContractInfoOf, Module, Event,
	TombstoneContractInfo, Config, CodeHash, Error,
	storage::Storage, wasm::PrefabWasmModule, exec::Executable,
};
use sp_std::prelude::*;
use sp_io::hashing::blake2_256;
use sp_core::crypto::UncheckedFrom;
use frame_support::{
	debug,
	storage::child,
	traits::{Currency, ExistenceRequirement, Get, OnUnbalanced, WithdrawReasons},
};
use pallet_contracts_primitives::{ContractAccessError, RentProjection, RentProjectionResult};
use sp_runtime::{
	DispatchError,
	traits::{Bounded, CheckedDiv, CheckedMul, SaturatedConversion, Saturating, Zero},
};

/// The amount to charge.
///
/// This amount respects the contract's rent allowance and the subsistence deposit.
/// Because of that, charging the amount cannot remove the contract.
struct OutstandingAmount<T: Config> {
	amount: BalanceOf<T>,
}

impl<T: Config> OutstandingAmount<T> {
	/// Create the new outstanding amount.
	///
	/// The amount should be always withdrawable and it should not kill the account.
	fn new(amount: BalanceOf<T>) -> Self {
		Self { amount }
	}

	/// Returns the amount this instance wraps.
	fn peek(&self) -> BalanceOf<T> {
		self.amount
	}

	/// Withdraws the outstanding amount from the given account.
	fn withdraw(self, account: &T::AccountId) {
		if let Ok(imbalance) = T::Currency::withdraw(
			account,
			self.amount,
			WithdrawReasons::FEE,
			ExistenceRequirement::KeepAlive,
		) {
			// This should never fail. However, let's err on the safe side.
			T::RentPayment::on_unbalanced(imbalance);
		}
	}
}

enum Verdict<T: Config> {
	/// The contract is exempted from paying rent.
	///
	/// For example, it already paid its rent in the current block, or it has enough deposit for not
	/// paying rent at all.
	Exempt,
	/// The contract cannot afford payment within its rent budget so it gets evicted. However,
	/// because its balance is greater than the subsistence threshold it leaves a tombstone.
	Evict {
		amount: Option<OutstandingAmount<T>>,
	},
	/// Everything is OK, we just only take some charge.
	Charge { amount: OutstandingAmount<T> },
}

pub struct Rent<T, E>(sp_std::marker::PhantomData<(T, E)>);

impl<T, E> Rent<T, E>
where
	T: Config,
	T::AccountId: UncheckedFrom<T::Hash> + AsRef<[u8]>,
	E: Executable<T>,
{
	/// Returns a fee charged per block from the contract.
	///
	/// This function accounts for the storage rent deposit. I.e. if the contract possesses enough funds
	/// then the fee can drop to zero.
	fn compute_fee_per_block(
		free_balance: &BalanceOf<T>,
		contract: &AliveContractInfo<T>,
		code_size_share: u32,
	) -> BalanceOf<T> {
		let uncovered_by_balance = T::DepositPerStorageByte::get()
			.saturating_mul(contract.storage_size.saturating_add(code_size_share).into())
			.saturating_add(
				T::DepositPerStorageItem::get()
					.saturating_mul(contract.pair_count.into())
			)
			.saturating_add(T::DepositPerContract::get())
			.saturating_sub(*free_balance);
		T::RentFraction::get().mul_ceil(uncovered_by_balance)
	}

	/// Returns amount of funds available to consume by rent mechanism.
	///
	/// Rent mechanism cannot consume more than `rent_allowance` set by the contract and it cannot make
	/// the balance lower than [`subsistence_threshold`].
	///
	/// In case the toal_balance is below the subsistence threshold, this function returns `None`.
	fn rent_budget(
		total_balance: &BalanceOf<T>,
		free_balance: &BalanceOf<T>,
		contract: &AliveContractInfo<T>,
	) -> Option<BalanceOf<T>> {
		let subsistence_threshold = Module::<T>::subsistence_threshold();
		// Reserved balance contributes towards the subsistence threshold to stay consistent
		// with the existential deposit where the reserved balance is also counted.
		if *total_balance < subsistence_threshold {
			return None;
		}

		// However, reserved balance cannot be charged so we need to use the free balance
		// to calculate the actual budget (which can be 0).
		let rent_allowed_to_charge = free_balance.saturating_sub(subsistence_threshold);
		Some(<BalanceOf<T>>::min(
			contract.rent_allowance,
			rent_allowed_to_charge,
		))
	}

	/// Consider the case for rent payment of the given account and returns a `Verdict`.
	///
	/// Use `handicap` in case you want to change the reference block number. (To get more details see
	/// `try_eviction` ).
	fn consider_case(
		account: &T::AccountId,
		current_block_number: T::BlockNumber,
		handicap: T::BlockNumber,
		contract: &AliveContractInfo<T>,
		code_size: u32,
	) -> Verdict<T> {
		// How much block has passed since the last deduction for the contract.
		let blocks_passed = {
			// Calculate an effective block number, i.e. after adjusting for handicap.
			let effective_block_number = current_block_number.saturating_sub(handicap);
			effective_block_number.saturating_sub(contract.deduct_block)
		};
		if blocks_passed.is_zero() {
			// Rent has already been paid
			return Verdict::Exempt;
		}

		let total_balance = T::Currency::total_balance(account);
		let free_balance = T::Currency::free_balance(account);

		// An amount of funds to charge per block for storage taken up by the contract.
		let fee_per_block = Self::compute_fee_per_block(&free_balance, contract, code_size);
		if fee_per_block.is_zero() {
			// The rent deposit offset reduced the fee to 0. This means that the contract
			// gets the rent for free.
			return Verdict::Exempt;
		}

		let rent_budget = match Self::rent_budget(&total_balance, &free_balance, contract) {
			Some(rent_budget) => rent_budget,
			None => {
				// All functions that allow a contract to transfer balance enforce
				// that the contract always stays above the subsistence threshold.
				// We want the rent system to always leave a tombstone to prevent the
				// accidental loss of a contract. Ony `seal_terminate` can remove a
				// contract without a tombstone. Therefore this case should be never
				// hit.
				debug::error!(
					"Tombstoned a contract that is below the subsistence threshold: {:?}",
					account
				);
				0u32.into()
			}
		};

		let dues = fee_per_block
			.checked_mul(&blocks_passed.saturated_into::<u32>().into())
			.unwrap_or_else(|| <BalanceOf<T>>::max_value());
		let insufficient_rent = rent_budget < dues;

		// If the rent payment cannot be withdrawn due to locks on the account balance, then evict the
		// account.
		//
		// NOTE: This seems problematic because it provides a way to tombstone an account while
		// avoiding the last rent payment. In effect, someone could retroactively set rent_allowance
		// for their contract to 0.
		let dues_limited = dues.min(rent_budget);
		let can_withdraw_rent = T::Currency::ensure_can_withdraw(
			account,
			dues_limited,
			WithdrawReasons::FEE,
			free_balance.saturating_sub(dues_limited),
		)
		.is_ok();

		if insufficient_rent || !can_withdraw_rent {
			// The contract cannot afford the rent payment and has a balance above the subsistence
			// threshold, so it leaves a tombstone.
			let amount = if can_withdraw_rent {
				Some(OutstandingAmount::new(dues_limited))
			} else {
				None
			};
			return Verdict::Evict { amount };
		}

		return Verdict::Charge {
			// We choose to use `dues_limited` here instead of `dues` just to err on the safer side.
			amount: OutstandingAmount::new(dues_limited),
		};
	}

	/// Enacts the given verdict and returns the updated `ContractInfo`.
	///
	/// `alive_contract_info` should be from the same address as `account`.
	///
	/// # Note
	///
	/// if `evictable_code` is `None` an `Evict` verdict will not be enacted. This is for
	/// when calling this function during a `call` where access to the soon to be evicted
	/// contract should be denied but storage should be left unmodified.
	fn enact_verdict(
		account: &T::AccountId,
		alive_contract_info: AliveContractInfo<T>,
		current_block_number: T::BlockNumber,
		verdict: Verdict<T>,
		evictable_code: Option<PrefabWasmModule<T>>,
	) -> Result<Option<AliveContractInfo<T>>, DispatchError> {
		match (verdict, evictable_code) {
			(Verdict::Exempt, _) => return Ok(Some(alive_contract_info)),
			(Verdict::Evict { amount }, Some(code)) => {
				// We need to remove the trie first because it is the only operation
				// that can fail and this function is called without a storage
				// transaction when called through `claim_surcharge`.
				Storage::<T>::queue_trie_for_deletion(&alive_contract_info)?;

				if let Some(amount) = amount {
					amount.withdraw(account);
				}

				// Note: this operation is heavy.
				let child_storage_root = child::root(
					&alive_contract_info.child_trie_info(),
				);

				let tombstone = <TombstoneContractInfo<T>>::new(
					&child_storage_root[..],
					alive_contract_info.code_hash,
				);
				let tombstone_info = ContractInfo::Tombstone(tombstone);
				<ContractInfoOf<T>>::insert(account, &tombstone_info);
				code.drop_from_storage();
				<Module<T>>::deposit_event(Event::Evicted(account.clone()));
				Ok(None)
			}
			(Verdict::Evict { amount: _ }, None) => {
				Ok(None)
			}
			(Verdict::Charge { amount }, _) => {
				let contract = ContractInfo::Alive(AliveContractInfo::<T> {
					rent_allowance: alive_contract_info.rent_allowance - amount.peek(),
					deduct_block: current_block_number,
					rent_payed: alive_contract_info.rent_payed.saturating_add(amount.peek()),
					..alive_contract_info
				});
				<ContractInfoOf<T>>::insert(account, &contract);
				amount.withdraw(account);
				Ok(Some(contract.get_alive().expect("We just constructed it as alive. qed")))
			}
		}
	}

	/// Make account paying the rent for the current block number
	///
	/// This functions does **not** evict the contract. It returns `None` in case the
	/// contract is in need of eviction. [`try_eviction`] must
	/// be called to perform the eviction.
	pub fn charge(
		account: &T::AccountId,
		contract: AliveContractInfo<T>,
		code_size: u32,
	) -> Result<Option<AliveContractInfo<T>>, DispatchError> {
		let current_block_number = <frame_system::Module<T>>::block_number();
		let verdict = Self::consider_case(
			account,
			current_block_number,
			Zero::zero(),
			&contract,
			code_size,
		);
		Self::enact_verdict(account, contract, current_block_number, verdict, None)
	}

	/// Process a report that a contract under the given address should be evicted.
	///
	/// Enact the eviction right away if the contract should be evicted and return the amount
	/// of rent that the contract payed over its lifetime.
	/// Otherwise, **do nothing** and return None.
	///
	/// The `handicap` parameter gives a way to check the rent to a moment in the past instead
	/// of current block. E.g. if the contract is going to be evicted at the current block,
	/// `handicap = 1` can defer the eviction for 1 block. This is useful to handicap certain snitchers
	/// relative to others.
	///
	/// NOTE this function performs eviction eagerly. All changes are read and written directly to
	/// storage.
	pub fn try_eviction(
		account: &T::AccountId,
		handicap: T::BlockNumber,
	) -> Result<(Option<BalanceOf<T>>, u32), DispatchError> {
		let contract = <ContractInfoOf<T>>::get(account);
		let contract = match contract {
			None | Some(ContractInfo::Tombstone(_)) => return Ok((None, 0)),
			Some(ContractInfo::Alive(contract)) => contract,
		};
		let module = PrefabWasmModule::<T>::from_storage_noinstr(contract.code_hash)?;
		let code_len = module.code_len();
		let current_block_number = <frame_system::Module<T>>::block_number();
		let verdict = Self::consider_case(
			account,
			current_block_number,
			handicap,
			&contract,
			module.occupied_storage(),
		);

		// Enact the verdict only if the contract gets removed.
		match verdict {
			Verdict::Evict { ref amount } => {
				// The outstanding `amount` is withdrawn inside `enact_verdict`.
				let rent_payed = amount
					.as_ref()
					.map(|a| a.peek())
					.unwrap_or_else(|| <BalanceOf<T>>::zero())
					.saturating_add(contract.rent_payed);
				Self::enact_verdict(
					account, contract, current_block_number, verdict, Some(module),
				)?;
				Ok((Some(rent_payed), code_len))
			}
			_ => Ok((None, code_len)),
		}
	}

	/// Returns the projected time a given contract will be able to sustain paying its rent. The
	/// returned projection is relevant for the current block, i.e. it is as if the contract was
	/// accessed at the beginning of the current block. Returns `None` in case if the contract was
	/// evicted before or as a result of the rent collection.
	///
	/// The returned value is only an estimation. It doesn't take into account any top ups, changing the
	/// rent allowance, or any problems coming from withdrawing the dues.
	///
	/// NOTE that this is not a side-effect free function! It will actually collect rent and then
	/// compute the projection. This function is only used for implementation of an RPC method through
	/// `RuntimeApi` meaning that the changes will be discarded anyway.
	pub fn compute_projection(
		account: &T::AccountId,
	) -> RentProjectionResult<T::BlockNumber> {
		use ContractAccessError::IsTombstone;

		let contract_info = <ContractInfoOf<T>>::get(account);
		let alive_contract_info = match contract_info {
			None | Some(ContractInfo::Tombstone(_)) => return Err(IsTombstone),
			Some(ContractInfo::Alive(contract)) => contract,
		};
		let module = PrefabWasmModule::from_storage_noinstr(alive_contract_info.code_hash)
			.map_err(|_| IsTombstone)?;
		let code_size = module.occupied_storage();
		let current_block_number = <frame_system::Module<T>>::block_number();
		let verdict = Self::consider_case(
			account,
			current_block_number,
			Zero::zero(),
			&alive_contract_info,
			code_size,
		);
		let new_contract_info = Self::enact_verdict(
			account, alive_contract_info, current_block_number, verdict, Some(module),
		);

		// Check what happened after enaction of the verdict.
		let alive_contract_info = match new_contract_info.map_err(|_| IsTombstone)? {
			None => return Err(IsTombstone),
			Some(contract) => contract,
		};

		// Compute how much would the fee per block be with the *updated* balance.
		let total_balance = T::Currency::total_balance(account);
		let free_balance = T::Currency::free_balance(account);
		let fee_per_block = Self::compute_fee_per_block(
			&free_balance, &alive_contract_info, code_size,
		);
		if fee_per_block.is_zero() {
			return Ok(RentProjection::NoEviction);
		}

		// Then compute how much the contract will sustain under these circumstances.
		let rent_budget = Self::rent_budget(&total_balance, &free_balance, &alive_contract_info).expect(
			"the contract exists and in the alive state;
			the updated balance must be greater than subsistence deposit;
			this function doesn't return `None`;
			qed
			",
		);
		let blocks_left = match rent_budget.checked_div(&fee_per_block) {
			Some(blocks_left) => blocks_left,
			None => {
				// `fee_per_block` is not zero here, so `checked_div` can return `None` if
				// there is an overflow. This cannot happen with integers though. Return
				// `NoEviction` here just in case.
				return Ok(RentProjection::NoEviction);
			}
		};

		let blocks_left = blocks_left.saturated_into::<u32>().into();
		Ok(RentProjection::EvictionAt(
			current_block_number + blocks_left,
		))
	}

	/// Restores the destination account using the origin as prototype.
	///
	/// The restoration will be performed iff:
	/// - the supplied code_hash does still exist on-chain
	/// - origin exists and is alive,
	/// - the origin's storage is not written in the current block
	/// - the restored account has tombstone
	/// - the tombstone matches the hash of the origin storage root, and code hash.
	///
	/// Upon succesful restoration, `origin` will be destroyed, all its funds are transferred to
	/// the restored account. The restored account will inherit the last write block and its last
	/// deduct block will be set to the current block.
	///
	/// # Return Value
	///
	/// Result<(CallerCodeSize, DestCodeSize), (DispatchError, CallerCodeSize, DestCodesize)>
	pub fn restore_to(
		origin: T::AccountId,
		dest: T::AccountId,
		code_hash: CodeHash<T>,
		rent_allowance: BalanceOf<T>,
		delta: Vec<crate::exec::StorageKey>,
	) -> Result<(u32, u32), (DispatchError, u32, u32)> {
		let mut origin_contract = <ContractInfoOf<T>>::get(&origin)
			.and_then(|c| c.get_alive())
			.ok_or((Error::<T>::InvalidSourceContract.into(), 0, 0))?;

		let child_trie_info = origin_contract.child_trie_info();

		let current_block = <frame_system::Module<T>>::block_number();

		if origin_contract.last_write == Some(current_block) {
			return Err((Error::<T>::InvalidContractOrigin.into(), 0, 0));
		}

		let dest_tombstone = <ContractInfoOf<T>>::get(&dest)
			.and_then(|c| c.get_tombstone())
			.ok_or((Error::<T>::InvalidDestinationContract.into(), 0, 0))?;

		let last_write = if !delta.is_empty() {
			Some(current_block)
		} else {
			origin_contract.last_write
		};

		// Fails if the code hash does not exist on chain
		let caller_code_len = E::add_user(code_hash).map_err(|e| (e, 0, 0))?;

		// We are allowed to eagerly modify storage even though the function can
		// fail later due to tombstones not matching. This is because the restoration
		// is always called from a contract and therefore in a storage transaction.
		// The failure of this function will lead to this transaction's rollback.
		let bytes_taken: u32 = delta.iter()
			.filter_map(|key| {
				let key = blake2_256(key);
				child::get_raw(&child_trie_info, &key).map(|value| {
					child::kill(&child_trie_info, &key);
					value.len() as u32
				})
			})
			.sum();

		let tombstone = <TombstoneContractInfo<T>>::new(
			// This operation is cheap enough because last_write (delta not included)
			// is not this block as it has been checked earlier.
			&child::root(&child_trie_info)[..],
			code_hash,
		);

		if tombstone != dest_tombstone {
			return Err((Error::<T>::InvalidTombstone.into(), caller_code_len, 0));
		}

		origin_contract.storage_size -= bytes_taken;

		<ContractInfoOf<T>>::remove(&origin);
		let tombstone_code_len = E::remove_user(origin_contract.code_hash);
		<ContractInfoOf<T>>::insert(&dest, ContractInfo::Alive(AliveContractInfo::<T> {
			trie_id: origin_contract.trie_id,
			storage_size: origin_contract.storage_size,
			pair_count: origin_contract.pair_count,
			code_hash,
			rent_allowance,
			rent_payed: <BalanceOf<T>>::zero(),
			deduct_block: current_block,
			last_write,
		}));

		let origin_free_balance = T::Currency::free_balance(&origin);
		T::Currency::make_free_balance_be(&origin, <BalanceOf<T>>::zero());
		T::Currency::deposit_creating(&dest, origin_free_balance);

		Ok((caller_code_len, tombstone_code_len))
	}
}
