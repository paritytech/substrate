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
	dispatch::Result, decl_event, decl_storage, decl_module,
	traits::{ArithmeticType, MakeTransactionPayment, TransferAsset, WithdrawReason}
};
use runtime_primitives::traits::{
	As, CheckedAdd, CheckedMul
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
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Fees {
		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee) config(): AssetOf<T>;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee) config(): AssetOf<T>;
	}
}

decl_event!(
	pub enum Event<T> where <T as system::Trait>::AccountId, Amount = AssetOf<T> {
		/// Transaction payment charged (transactor, fee_amount)
		TransactionPayment(AccountId, Amount),
	}
);

impl<T: Trait> MakeTransactionPayment<T::AccountId> for Module<T> {
	fn make_transaction_payment(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let bytes_fee = Self::transaction_byte_fee().checked_mul(
			&<AssetOf<T> as As<u64>>::sa(encoded_len as u64)
		).ok_or_else(|| "bytes fee overflow")?;
		let overall = Self::transaction_base_fee().checked_add(&bytes_fee).ok_or_else(|| "bytes fee overflow")?;

		T::TransferAsset::withdraw(transactor, overall, WithdrawReason::TransactionPayment)?;
		Self::deposit_event(RawEvent::TransactionPayment(transactor.clone(), overall));

		Ok(())
	}
}
