// Copyright 2019 Parity Technologies (UK) Ltd.
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

use crate::{BalanceOf, ContractInfo, ContractInfoOf, TombstoneContractInfo, Trait, AliveContractInfo, CodeHash, RawAliveContractInfo, exec};
use sp_runtime::traits::{Bounded, CheckedDiv, CheckedMul, Saturating, Zero,
	SaturatedConversion};
use support::storage::child;
use support::traits::{Currency, ExistenceRequirement, Get, WithdrawReason, OnUnbalanced};
use support::StorageMap;
use primitives::blake2_256;

#[derive(PartialEq, Eq, Copy, Clone)]
#[must_use]
pub enum RentOutcome {
	/// Exempted from rent iff:
	/// * rent is offset completely by the `rent_deposit_offset`,
	/// * or rent has already been paid for this block number,
	/// * or account doesn't have a contract,
	/// * or account has a tombstone.
	Exempted,
	/// Evicted iff:
	/// * rent exceed rent allowance,
	/// * or can't withdraw the rent,
	/// * or go below subsistence threshold.
	Evicted,
	/// The outstanding dues were paid or were able to be paid.
	Ok,
}

/// Evict and optionally pay dues (or check account can pay them otherwise) at the current
/// block number (modulo `handicap`, read on).
///
/// Returns `None` if the account has no contract info or it was removed along with its
/// `ContractInfo` due to dropping its balance below the subsistence threshold.
///
/// `pay_rent` gives an ability to pay or skip paying rent.
/// `handicap` gives a way to check or pay the rent up to a moment in the past instead
/// of current block.
///
/// NOTE: This function acts eagerly, all modification are committed into the storage.
fn try_evict_or_and_pay_rent<T: Trait>(
	account: &T::AccountId,
	handicap: T::BlockNumber,
	pay_rent: bool,
) -> (RentOutcome, Option<ContractInfo<T>>) {
	let contract_info = <ContractInfoOf<T>>::get(account);
	let contract = match contract_info {
		// We don't collect rent from non-contract accounts and tombstones.
		None | Some(ContractInfo::Tombstone(_)) => return (RentOutcome::Exempted, contract_info),
		Some(ContractInfo::Alive(contract)) => contract,
	};

	let current_block_number = <system::Module<T>>::block_number();

	// How much block has passed since the last deduction for the contract.
	let blocks_passed = {
		// Calculate an effective block number, i.e. after adjusting for handicap.
		let effective_block_number = current_block_number.saturating_sub(handicap);
		let n = effective_block_number.saturating_sub(contract.deduct_block);
		if n.is_zero() {
			// Rent has already been paid
			return (RentOutcome::Exempted, Some(ContractInfo::Alive(contract)));
		}
		n
	};

	let balance = T::Currency::free_balance(account);

	// An amount of funds to charge per block for storage taken up by the contract.
	let fee_per_block = {
		let free_storage = balance
			.checked_div(&T::RentDepositOffset::get())
			.unwrap_or_else(Zero::zero);

		let effective_storage_size =
			<BalanceOf<T>>::from(contract.storage_size).saturating_sub(free_storage);

		effective_storage_size
			.checked_mul(&T::RentByteFee::get())
			.unwrap_or(<BalanceOf<T>>::max_value())
	};

	if fee_per_block.is_zero() {
		// The rent deposit offset reduced the fee to 0. This means that the contract
		// gets the rent for free.
		return (RentOutcome::Exempted, Some(ContractInfo::Alive(contract)));
	}

	// The minimal amount of funds required for a contract not to be evicted.
	let subsistence_threshold = T::Currency::minimum_balance() + T::TombstoneDeposit::get();

	if balance < subsistence_threshold {
		// The contract cannot afford to leave a tombstone, so remove the contract info altogether.
		<ContractInfoOf<T>>::remove(account);
		sp_io::storage::child_storage_kill(&contract.trie_id);
		return (RentOutcome::Evicted, None);
	}

	let dues = fee_per_block
		.checked_mul(&blocks_passed.saturated_into::<u32>().into())
		.unwrap_or(<BalanceOf<T>>::max_value());
	let rent_budget = contract.rent_allowance.min(balance - subsistence_threshold);
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
		WithdrawReason::Fee.into(),
		balance.saturating_sub(dues_limited),
	)
	.is_ok();

	if can_withdraw_rent && (insufficient_rent || pay_rent) {
		// Collect dues.
		let imbalance = T::Currency::withdraw(
			account,
			dues_limited,
			WithdrawReason::Fee.into(),
			ExistenceRequirement::KeepAlive,
		)
		.expect(
			"Withdraw has been checked above;
			dues_limited < rent_budget < balance - subsistence < balance - existential_deposit;
			qed",
		);

		T::RentPayment::on_unbalanced(imbalance);
	}

	if insufficient_rent || !can_withdraw_rent {
		// The contract cannot afford the rent payment and has a balance above the subsistence
		// threshold, so it leaves a tombstone.

		// Note: this operation is heavy.
		let child_storage_root = sp_io::storage::child_root(&contract.trie_id);

		let tombstone = <TombstoneContractInfo<T>>::new(
			&child_storage_root[..],
			contract.code_hash,
		);
		let tombstone_info = ContractInfo::Tombstone(tombstone);
		<ContractInfoOf<T>>::insert(account, &tombstone_info);

		sp_io::storage::child_storage_kill(&contract.trie_id);

		return (RentOutcome::Evicted, Some(tombstone_info));
	}

	if pay_rent {
		let contract_info = ContractInfo::Alive(AliveContractInfo::<T> {
			rent_allowance: contract.rent_allowance - dues, // rent_allowance is not exceeded
			deduct_block: current_block_number,
			..contract
		});

		<ContractInfoOf<T>>::insert(account, &contract_info);

		return (RentOutcome::Ok, Some(contract_info));
	}

	(RentOutcome::Ok, Some(ContractInfo::Alive(contract)))
}

/// Make account paying the rent for the current block number
///
/// Returns `None` if the account has no contract info or it was removed along with its
/// `ContractInfo` due to dropping its balance below the subsistence threshold.
///
/// NOTE: This function acts eagerly.
pub fn pay_rent<T: Trait>(account: &T::AccountId) -> Option<ContractInfo<T>> {
	try_evict_or_and_pay_rent::<T>(account, Zero::zero(), true).1
}

/// Evict the account if it should be evicted at the given block number.
///
/// `handicap` gives a way to check or pay the rent up to a moment in the past instead
/// of current block. E.g. if the contract is going to be evicted at the current block,
/// `handicap=1` can defer the eviction for 1 block.
///
/// NOTE: This function acts eagerly.
pub fn try_evict<T: Trait>(account: &T::AccountId, handicap: T::BlockNumber) -> RentOutcome {
	try_evict_or_and_pay_rent::<T>(account, handicap, false).0
}

/// Restores the destination account using the origin as prototype.
///
/// The restoration will be performed iff:
/// - origin exists and is alive,
/// - the origin's storage is not written in the current block
/// - the restored account has tombstone
/// - the tombstone matches the hash of the origin storage root, and code hash.
///
/// Upon succesful restoration, `origin` will be destroyed, all its funds are transferred to
/// the restored account. The restored account will inherit the last write block and its last
/// deduct block will be set to the current block.
pub fn restore_to<T: Trait>(
	origin: T::AccountId,
	dest: T::AccountId,
	code_hash: CodeHash<T>,
	rent_allowance: BalanceOf<T>,
	delta: Vec<exec::StorageKey>,
) -> Result<(), &'static str> {
	let mut origin_contract = <ContractInfoOf<T>>::get(&origin)
		.and_then(|c| c.get_alive())
		.ok_or("Cannot restore from inexisting or tombstone contract")?;

	let current_block = <system::Module<T>>::block_number();

	if origin_contract.last_write == Some(current_block) {
		return Err("Origin TrieId written in the current block");
	}

	let dest_tombstone = <ContractInfoOf<T>>::get(&dest)
		.and_then(|c| c.get_tombstone())
		.ok_or("Cannot restore to inexisting or alive contract")?;

	let last_write = if !delta.is_empty() {
		Some(current_block)
	} else {
		origin_contract.last_write
	};

	let key_values_taken = delta.iter()
		.filter_map(|key| {
			child::get_raw(&origin_contract.trie_id, &blake2_256(key)).map(|value| {
				child::kill(&origin_contract.trie_id, &blake2_256(key));
				(key, value)
			})
		})
		.collect::<Vec<_>>();

	let tombstone = <TombstoneContractInfo<T>>::new(
		// This operation is cheap enough because last_write (delta not included)
		// is not this block as it has been checked earlier.
		&sp_io::storage::child_root(&origin_contract.trie_id)[..],
		code_hash,
	);

	if tombstone != dest_tombstone {
		for (key, value) in key_values_taken {
			child::put_raw(&origin_contract.trie_id, &blake2_256(key), &value);
		}

		return Err("Tombstones don't match");
	}

	origin_contract.storage_size -= key_values_taken.iter()
		.map(|(_, value)| value.len() as u32)
		.sum::<u32>();

	<ContractInfoOf<T>>::remove(&origin);
	<ContractInfoOf<T>>::insert(&dest, ContractInfo::Alive(RawAliveContractInfo {
		trie_id: origin_contract.trie_id,
		storage_size: origin_contract.storage_size,
		code_hash,
		rent_allowance,
		deduct_block: current_block,
		last_write,
	}));

	let origin_free_balance = T::Currency::free_balance(&origin);
	T::Currency::make_free_balance_be(&origin, <BalanceOf<T>>::zero());
	T::Currency::deposit_creating(&dest, origin_free_balance);

	Ok(())
}
