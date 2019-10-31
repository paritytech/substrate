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

use crate::{BalanceOf, ContractInfo, ContractInfoOf, TombstoneContractInfo, Trait, AliveContractInfo};
use sr_primitives::traits::{Bounded, CheckedDiv, CheckedMul, Saturating, Zero,
	SaturatedConversion};
use support::traits::{Currency, ExistenceRequirement, Get, WithdrawReason, OnUnbalanced};
use support::StorageMap;

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
		runtime_io::kill_child_storage(&contract.trie_id);
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
		let child_storage_root = runtime_io::child_storage_root(&contract.trie_id);

		let tombstone = <TombstoneContractInfo<T>>::new(
			&child_storage_root[..],
			contract.code_hash,
		);
		let tombstone_info = ContractInfo::Tombstone(tombstone);
		<ContractInfoOf<T>>::insert(account, &tombstone_info);

		runtime_io::kill_child_storage(&contract.trie_id);

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
