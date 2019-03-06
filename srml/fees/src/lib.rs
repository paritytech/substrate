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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Handles all transaction fee related operations

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use srml_support::{
	dispatch::Result, StorageMap, decl_event, decl_storage, decl_module,
	traits::{ArithmeticType, ChargeBytesFee, ChargeFee, TransferAsset, WithdrawReason}
};
use runtime_primitives::traits::{
	As, CheckedAdd, CheckedSub, CheckedMul, Zero
};
use system;

mod mock;
mod tests;

type AssetOf<T> = <<T as Trait>::TransferAsset as ArithmeticType>::Type;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// A function does the asset transfer between accounts
	type TransferAsset: ArithmeticType + TransferAsset<Self::AccountId, Amount=AssetOf<Self>>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn on_finalise() {
			let extrinsic_count = <system::Module<T>>::extrinsic_count();
			(0..extrinsic_count).for_each(|index| {
				// Deposit `Charged` event if some amount of fee charged.
				let fee = <CurrentTransactionFee<T>>::take(index);
				if !fee.is_zero() {
					Self::deposit_event(RawEvent::Charged(index, fee));
				}
			});
		}
	}
}

decl_event!(
	pub enum Event<T> where Amount = AssetOf<T> {
		/// Fee charged (extrinsic_index, fee_amount)
		Charged(u32, Amount),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Fees {
		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee) config(): AssetOf<T>;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee) config(): AssetOf<T>;

		/// The `extrinsic_index => accumulated_fees` map, containing records to
		/// track the overall charged fees for each transaction.
		///
		/// All records should be removed at finalise stage.
		CurrentTransactionFee get(current_transaction_fee): map u32 => AssetOf<T>;
	}
}

impl<T: Trait> ChargeBytesFee<T::AccountId> for Module<T> {
	fn charge_base_bytes_fee(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let bytes_fee = Self::transaction_byte_fee().checked_mul(
			&<AssetOf<T> as As<u64>>::sa(encoded_len as u64)
		).ok_or_else(|| "bytes fee overflow")?;
		let overall = Self::transaction_base_fee().checked_add(&bytes_fee).ok_or_else(|| "bytes fee overflow")?;
		Self::charge_fee(transactor, overall)
	}
}

impl<T: Trait> ChargeFee<T::AccountId> for Module<T> {
	type Amount = AssetOf<T>;

	fn charge_fee(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
		let extrinsic_index = <system::Module<T>>::extrinsic_index().ok_or_else(|| "no extrinsic index found")?;
		let current_fee = Self::current_transaction_fee(extrinsic_index);
		let new_fee = current_fee.checked_add(&amount).ok_or_else(|| "fee got overflow after charge")?;

		T::TransferAsset::withdraw(transactor, amount, WithdrawReason::TransactionPayment)?;

		<CurrentTransactionFee<T>>::insert(extrinsic_index, new_fee);
		Ok(())
	}

	fn refund_fee(transactor: &T::AccountId, amount: AssetOf<T>) -> Result {
		let extrinsic_index = <system::Module<T>>::extrinsic_index().ok_or_else(|| "no extrinsic index found")?;
		let current_fee = Self::current_transaction_fee(extrinsic_index);
		let new_fee = current_fee.checked_sub(&amount).ok_or_else(|| "fee got underflow after refund")?;

		T::TransferAsset::deposit(transactor, amount)?;

		<CurrentTransactionFee<T>>::insert(extrinsic_index, new_fee);
		Ok(())
	}
}
