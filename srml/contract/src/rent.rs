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
use runtime_primitives::traits::{As, Bounded, CheckedDiv, CheckedMul, Saturating, Zero};
use srml_support::traits::{Currency, ExistenceRequirement, Imbalance, WithdrawReason};
use srml_support::StorageMap;

/// Evict and optionally pay dues (or check account can pay them otherwise), for given block number.
/// Return true iff the account has been evicted.
///
/// Exempted from rent iff:
/// * rent is offset completely by the `rent_deposit_offset`,
/// * or rent has already been paid for this block number,
/// * or account doesn't have a contract,
/// * or account has a tombstone.
///
/// Evicted iff:
/// * rent exceed rent allowance,
/// * or can't withdraw the rent,
/// * or go below subsistence threshold.
///
/// This function acts eagerly, all modification are committed into storages.
fn try_evict_or_and_pay_rent<T: Trait>(
	account: &T::AccountId,
	block_number: T::BlockNumber,
	pay_rent: bool,
) -> bool {
	let contract = match <ContractInfoOf<T>>::get(account) {
		None | Some(ContractInfo::Tombstone(_)) => return false,
		Some(ContractInfo::Alive(contract)) => contract,
	};

	// Rent has already been paid
	if contract.deduct_block >= block_number {
		return false;
	}

	let balance = T::Currency::free_balance(account);

	let free_storage = balance
		.checked_div(&<Module<T>>::rent_deposit_offset())
		.unwrap_or(<BalanceOf<T>>::sa(0));

	let effective_storage_size =
		<BalanceOf<T>>::sa(contract.storage_size).saturating_sub(free_storage);

	let fee_per_block = effective_storage_size
		.checked_mul(&<Module<T>>::rent_byte_price())
		.unwrap_or(<BalanceOf<T>>::max_value());

	if fee_per_block.is_zero() {
		// The rent deposit offset reduced the fee to 0. This means that the contract
		// gets the rent for free.
		return false;
	}

	let blocks_to_rent = block_number.saturating_sub(contract.deduct_block);
	let rent = fee_per_block
		.checked_mul(&<BalanceOf<T>>::sa(blocks_to_rent.as_()))
		.unwrap_or(<BalanceOf<T>>::max_value());
	let subsistence_threshold = T::Currency::minimum_balance() + <Module<T>>::tombstone_deposit();

	let rent_limited = rent.min(contract.rent_allowance);

	let rent_allowance_exceeded = rent > contract.rent_allowance;
	let is_below_subsistence = balance < subsistence_threshold;
	let go_below_subsistence = balance.saturating_sub(rent_limited) < subsistence_threshold;
	let can_withdraw_rent = T::Currency::ensure_can_withdraw(
		account,
		rent_limited,
		WithdrawReason::Fee,
		balance.saturating_sub(rent_limited),
	).is_ok();

	if !rent_allowance_exceeded && can_withdraw_rent && !go_below_subsistence {
		// Collect dues

		if pay_rent {
			let imbalance = T::Currency::withdraw(
				account,
				rent,
				WithdrawReason::Fee,
				ExistenceRequirement::KeepAlive,
			)
			.expect(
				"Withdraw has been checked above;
				go_below_subsistence is false and subsistence > existencial_deposit;
				qed",
			);

			<ContractInfoOf<T>>::mutate(account, |contract| {
				contract
					.as_mut()
					.and_then(|c| c.as_alive_mut())
					.expect("Dead or inexistent account has been exempt above; qed")
					.rent_allowance -= imbalance.peek(); // rent_allowance is not exceeded
			})
		}
		return false;
	} else {
		// Evict

		if can_withdraw_rent && !go_below_subsistence {
			T::Currency::withdraw(
				account,
				rent,
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
			// Note: this operation is heavy.
			// Note: if the storage hasn't been touched then it returns None, which is OK.
			let child_storage_root = runtime_io::child_storage_root(&contract.trie_id);

			let tombstone = TombstoneContractInfo::new(
				child_storage_root,
				contract.storage_size,
				contract.code_hash,
			);
			<ContractInfoOf<T>>::insert(account, ContractInfo::Tombstone(tombstone));
			runtime_io::kill_child_storage(&contract.trie_id);
		}

		return true;
	}
}

/// Make account paying the rent for the current block number
///
/// Call try_evict_or_and_pay_rent with setting pay rent to true
pub fn pay_rent<T: Trait>(account: &T::AccountId) {
	try_evict_or_and_pay_rent::<T>(account, <system::Module<T>>::block_number(), true);
}

/// Evict the account if he should be evicted at the given block number.
/// Return true iff the account has been evicted.
///
/// Call try_evict_or_and_pay_rent with setting pay rent to false
pub fn try_evict_at<T: Trait>(account: &T::AccountId, block: T::BlockNumber) -> bool {
	try_evict_or_and_pay_rent::<T>(account, block, false)
}
