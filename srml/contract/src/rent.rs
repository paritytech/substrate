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

use crate::{BalanceOf, ContractInfo, ContractInfoOf, Module, TombstoneContractInfo, Trait};
use runtime_primitives::traits::{Bounded, CheckedDiv, CheckedMul, Saturating, Zero,
	SaturatedConversion};
use srml_support::traits::{Currency, ExistenceRequirement, Imbalance, WithdrawReason};
use srml_support::StorageMap;

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
) -> RentOutcome {
	let contract = match <ContractInfoOf<T>>::get(account) {
		None | Some(ContractInfo::Tombstone(_)) => return RentOutcome::Exempted,
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
			return RentOutcome::Exempted;
		}
		n
	};

	let balance = T::Currency::free_balance(account);

	// An amount of funds to charge per block for storage taken up by the contract.
	let fee_per_block = {
		let free_storage = balance
			.checked_div(&<Module<T>>::rent_deposit_offset())
			.unwrap_or_else(Zero::zero);

		let effective_storage_size =
			<BalanceOf<T>>::from(contract.storage_size).saturating_sub(free_storage);

		effective_storage_size
			.checked_mul(&<Module<T>>::rent_byte_price())
			.unwrap_or(<BalanceOf<T>>::max_value())
	};

	if fee_per_block.is_zero() {
		// The rent deposit offset reduced the fee to 0. This means that the contract
		// gets the rent for free.
		return RentOutcome::Exempted;
	}

	// The minimal amount of funds required for a contract not to be evicted.
	let subsistence_threshold = T::Currency::minimum_balance() + <Module<T>>::tombstone_deposit();

	let dues = fee_per_block
		.checked_mul(&blocks_passed.saturated_into::<u32>().into())
		.unwrap_or(<BalanceOf<T>>::max_value());

	let dues_limited = dues.min(contract.rent_allowance);
	let rent_allowance_exceeded = dues > contract.rent_allowance;
	let is_below_subsistence = balance < subsistence_threshold;
	let go_below_subsistence = balance.saturating_sub(dues_limited) < subsistence_threshold;
	let can_withdraw_rent = T::Currency::ensure_can_withdraw(
		account,
		dues_limited,
		WithdrawReason::Fee,
		balance.saturating_sub(dues_limited),
	)
	.is_ok();

	if !rent_allowance_exceeded && can_withdraw_rent && !go_below_subsistence {
		// Collect dues

		if pay_rent {
			let imbalance = T::Currency::withdraw(
				account,
				dues,
				WithdrawReason::Fee,
				ExistenceRequirement::KeepAlive,
			)
			.expect(
				"Withdraw has been checked above;
				go_below_subsistence is false and subsistence > existencial_deposit;
				qed",
			);

			<ContractInfoOf<T>>::mutate(account, |contract| {
				let contract = contract
					.as_mut()
					.and_then(|c| c.as_alive_mut())
					.expect("Dead or inexistent account has been exempt above; qed");

				contract.rent_allowance -= imbalance.peek(); // rent_allowance is not exceeded
				contract.deduct_block = current_block_number;
			})
		}

		RentOutcome::Ok
	} else {
		// Evict

		if can_withdraw_rent && !go_below_subsistence {
			T::Currency::withdraw(
				account,
				dues,
				WithdrawReason::Fee,
				ExistenceRequirement::KeepAlive,
			)
			.expect("Can withdraw and don't go below subsistence");
		} else if !is_below_subsistence {
			T::Currency::make_free_balance_be(account, subsistence_threshold);
		} else {
			T::Currency::make_free_balance_be(account, <BalanceOf<T>>::zero());
		}

		if !is_below_subsistence {
			// The contract has funds above subsistence deposit and that means it can afford to
			// leave tombstone.

			// Note: this operation is heavy.
			let child_storage_root = runtime_io::child_storage_root(&contract.trie_id);

			let tombstone = <TombstoneContractInfo<T>>::new(
				&child_storage_root[..],
				contract.code_hash,
			);
			<ContractInfoOf<T>>::insert(account, ContractInfo::Tombstone(tombstone));
			runtime_io::kill_child_storage(&contract.trie_id);
		}

		RentOutcome::Evicted
	}
}

/// Make account paying the rent for the current block number
///
/// NOTE: This function acts eagerly.
pub fn pay_rent<T: Trait>(account: &T::AccountId) {
	let _ = try_evict_or_and_pay_rent::<T>(account, Zero::zero(), true);
}

/// Evict the account if it should be evicted at the given block number.
///
/// `handicap` gives a way to check or pay the rent up to a moment in the past instead
/// of current block. E.g. if the contract is going to be evicted at the current block,
/// `handicap=1` can defer the eviction for 1 block.
///
/// NOTE: This function acts eagerly.
pub fn try_evict<T: Trait>(account: &T::AccountId, handicap: T::BlockNumber) -> RentOutcome {
	try_evict_or_and_pay_rent::<T>(account, handicap, false)
}
