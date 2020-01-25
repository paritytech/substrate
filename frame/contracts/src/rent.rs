// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use crate::{
	AliveContractInfo, BalanceOf, ContractInfo, ContractInfoOf, Module, RawEvent,
	TombstoneContractInfo, Trait,
};
use frame_support::storage::child;
use frame_support::traits::{Currency, ExistenceRequirement, Get, OnUnbalanced, WithdrawReason};
use frame_support::StorageMap;
use sp_runtime::traits::{Bounded, CheckedDiv, CheckedMul, SaturatedConversion, Saturating, Zero};

/// The amount to charge.
///
/// This amount respects the contract's rent allowance and the subsistence deposit.
/// Because of that, charging the amount cannot remove the contract.
struct OutstandingAmount<T: Trait> {
	amount: BalanceOf<T>,
}

impl<T: Trait> OutstandingAmount<T> {
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
			WithdrawReason::Fee.into(),
			ExistenceRequirement::KeepAlive,
		) {
			// This should never fail. However, let's err on the safe side.
			T::RentPayment::on_unbalanced(imbalance);
		}
	}
}

enum Verdict<T: Trait> {
	/// The contract is exempted from paying rent.
	///
	/// For example, it already paid its rent in the current block, or it has enough deposit for not
	/// paying rent at all.
	Exempt,
	/// Funds dropped below the subsistence deposit.
	///
	/// Remove the contract along with it's storage.
	Kill,
	/// The contract cannot afford payment within its rent budget so it gets evicted. However,
	/// because its balance is greater than the subsistence threshold it leaves a tombstone.
	Evict {
		amount: Option<OutstandingAmount<T>>,
	},
	/// Everything is OK, we just only take some charge.
	Charge {
		amount: OutstandingAmount<T>,
	},
}

/// Consider the case for rent payment of the given account and returns a `Verdict`.
///
/// The `current_block_number` must be equal to the current block number. Use `handicap` do
/// change the reference block number. (See `snitch_contract_should_be_evicted` for more details).
fn consider_case<T: Trait>(
	account: &T::AccountId,
	current_block_number: T::BlockNumber,
	handicap: T::BlockNumber,
	contract: &AliveContractInfo<T>,
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
		return Verdict::Exempt;
	}

	// The minimal amount of funds required for a contract not to be evicted.
	let subsistence_threshold = T::Currency::minimum_balance() + T::TombstoneDeposit::get();

	if balance < subsistence_threshold {
		// The contract cannot afford to leave a tombstone, so remove the contract info altogether.
		return Verdict::Kill;
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
fn enact_verdict<T: Trait>(
	account: &T::AccountId,
	alive_contract_info: AliveContractInfo<T>,
	current_block_number: T::BlockNumber,
	verdict: Verdict<T>,
) -> Option<ContractInfo<T>> {
	match verdict {
		Verdict::Exempt => return Some(ContractInfo::Alive(alive_contract_info)),
		Verdict::Kill => {
			<ContractInfoOf<T>>::remove(account);
			child::kill_storage(
				&alive_contract_info.trie_id,
				alive_contract_info.child_trie_unique_id(),
			);
			<Module<T>>::deposit_event(RawEvent::Evicted(account.clone(), false));
			None
		}
		Verdict::Evict { amount } => {
			if let Some(amount) = amount {
				amount.withdraw(account);
			}

			// Note: this operation is heavy.
			let child_storage_root = child::child_root(&alive_contract_info.trie_id);

			let tombstone = <TombstoneContractInfo<T>>::new(
				&child_storage_root[..],
				alive_contract_info.code_hash,
			);
			let tombstone_info = ContractInfo::Tombstone(tombstone);
			<ContractInfoOf<T>>::insert(account, &tombstone_info);

			child::kill_storage(
				&alive_contract_info.trie_id,
				alive_contract_info.child_trie_unique_id(),
			);

			<Module<T>>::deposit_event(RawEvent::Evicted(account.clone(), true));
			Some(tombstone_info)
		}
		Verdict::Charge { amount } => {
			let contract_info = ContractInfo::Alive(AliveContractInfo::<T> {
				rent_allowance: alive_contract_info.rent_allowance - amount.peek(),
				deduct_block: current_block_number,
				..alive_contract_info
			});
			<ContractInfoOf<T>>::insert(account, &contract_info);

			amount.withdraw(account);
			Some(contract_info)
		}
	}
}

/// Make account paying the rent for the current block number
///
/// NOTE this function performs eviction eagerly. All changes are read and written directly to
/// storage.
pub fn collect_rent<T: Trait>(account: &T::AccountId) -> Option<ContractInfo<T>> {
	let contract_info = <ContractInfoOf<T>>::get(account);
	let alive_contract_info = match contract_info {
		None | Some(ContractInfo::Tombstone(_)) => return contract_info,
		Some(ContractInfo::Alive(contract)) => contract,
	};

	let current_block_number = <frame_system::Module<T>>::block_number();
	let verdict = consider_case::<T>(
		account,
		current_block_number,
		Zero::zero(),
		&alive_contract_info,
	);
	enact_verdict(account, alive_contract_info, current_block_number, verdict)
}

/// Process a snitch that a contract under the given address should be evicted.
///
/// Enact the eviction right away if the contract should be evicted and return true.
/// Otherwise, **do nothing** and return false.
///
/// The `handicap` parameter gives a way to check the rent to a moment in the past instead
/// of current block. E.g. if the contract is going to be evicted at the current block,
/// `handicap = 1` can defer the eviction for 1 block. This is useful to handicap certain snitchers
/// relative to others.
///
/// NOTE this function performs eviction eagerly. All changes are read and written directly to
/// storage.
pub fn snitch_contract_should_be_evicted<T: Trait>(
	account: &T::AccountId,
	handicap: T::BlockNumber,
) -> bool {
	let contract_info = <ContractInfoOf<T>>::get(account);
	let alive_contract_info = match contract_info {
		None | Some(ContractInfo::Tombstone(_)) => return false,
		Some(ContractInfo::Alive(contract)) => contract,
	};
	let current_block_number = <frame_system::Module<T>>::block_number();
	let verdict = consider_case::<T>(
		account,
		current_block_number,
		handicap,
		&alive_contract_info,
	);

	// Enact the verdict only if the contract gets removed.
	match verdict {
		Verdict::Kill => {
			enact_verdict(account, alive_contract_info, current_block_number, verdict);
			true
		}
		Verdict::Evict { .. } => {
			enact_verdict(account, alive_contract_info, current_block_number, verdict);
			true
		}
		_ => false,
	}
}
