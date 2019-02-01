// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

#[macro_use]
extern crate srml_support as runtime_support;

use parity_codec_derive::{Encode, Decode};

use runtime_support::{Parameter, dispatch::Result};
use runtime_primitives::traits::{Member, SimpleArithmetic, ChargeBytesFee, ChargeFee, TransferAsset};

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The unit for fee amount
	type Amount: Member + Parameter + SimpleArithmetic + Default + Copy;

	/// A function does the asset transfer between accounts
	type TransferAsset: TransferAsset<Self::AccountId, Amount = Self::Amount>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn on_finalise() {
			// TODO: read CurrentTransactionFee, deposit events, kill storage
		}
	}
}

decl_event!(
	pub enum Event<T> where <T as Trait>::Amount {
		/// Fee charged (extrinsic_index, fee_amount)
		Charged(u32, Amount),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as Assets {
		/// The fee to be paid for making a transaction; the base.
		pub TransactionBaseFee get(transaction_base_fee) config(): T::Amount;
		/// The fee to be paid for making a transaction; the per-byte portion.
		pub TransactionByteFee get(transaction_byte_fee) config(): T::Amount;

		CurrentTransactionFee: map u32 => T::Amount;
	}
}

impl<T: Trait> ChargeBytesFee<T::AccountId> for Module<T> {
	fn charge_base_bytes_fee(transactor: &T::AccountId, len: usize) -> Result {
		// TODO: update CurrentTransactionFee, make transfer
		Ok(())
	}
}

impl<T: Trait> ChargeFee<T::AccountId> for Module<T> {
	type Amount = T::Amount;

	fn charge_fee(transactor: &T::AccountId, amount: T::Amount) -> Result {
		// TODO: update CurrentTransactionFee, make transfer
		Ok(())
	}

	fn refund_fee(transactor: &T::AccountId, amount: T::Amount) {
		// TODO: update CurrentTransactionFee, make transfer
	}
}
