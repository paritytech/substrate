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

use runtime_support::{Parameter, dispatch::Result, StorageMap};
use runtime_primitives::traits::{As, Member, SimpleArithmetic, ChargeBytesFee, ChargeFee, TransferAsset};
use system;

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The unit for fee amount
	type Amount: Member + Parameter + SimpleArithmetic + Default + Copy + As<u64>;

	/// A function does the asset transfer between accounts
	type TransferAsset: TransferAsset<Self::AccountId, Amount = Self::Amount>;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event<T>() = default;

		fn on_finalise() {
			let extrinsic_count = match <system::Module<T>>::extrinsic_count() {
				Some(extrinsic_count) => extrinsic_count,
				None => return,
			};
			(0..extrinsic_count).for_each(|index| {
				Self::deposit_event(RawEvent::Charged(index.clone(), Self::current_transaction_fee(index.clone())));
				<CurrentTransactionFee<T>>::remove(index);
			});
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

		/// The `extrinsic_index => accumulated_fees` map, containing records to
		/// track the overall charged fees for each transaction.
		///
		/// All records should be removed at finalise stage.
		CurrentTransactionFee get(current_transaction_fee): map u32 => T::Amount;
	}
}

impl<T: Trait> ChargeBytesFee<T::AccountId> for Module<T> {
	fn charge_base_bytes_fee(transactor: &T::AccountId, encoded_len: usize) -> Result {
		let fee = Self::transaction_base_fee() + Self::transaction_base_fee() * <T::Amount as As<u64>>::sa(encoded_len as u64);
		Self::charge_fee(transactor, fee)
	}
}

impl<T: Trait> ChargeFee<T::AccountId> for Module<T> {
	type Amount = T::Amount;

	fn charge_fee(transactor: &T::AccountId, amount: T::Amount) -> Result {
		T::TransferAsset::transfer_from(transactor, amount).and_then(|_| {
			match <system::Module<T>>::extrinsic_index() {
				Some(extrinsic_index) => {
					let current_fee = Self::current_transaction_fee(extrinsic_index);
					<CurrentTransactionFee<T>>::insert(extrinsic_index, current_fee + amount);
					Ok(())
				},
				// TODO: how do we deal with no extrinsic index?
				None => return Err("No extrinsic index found.")
			}
		})
	}

	fn refund_fee(transactor: &T::AccountId, amount: T::Amount) -> Result {
		T::TransferAsset::transfer_to(transactor, amount).and_then(|_| {
			match <system::Module<T>>::extrinsic_index() {
				Some(extrinsic_index) => {
					let current_fee = Self::current_transaction_fee(extrinsic_index);
					<CurrentTransactionFee<T>>::insert(extrinsic_index, current_fee - amount);
					Ok(())
				},
				// TODO: how do we deal with no extrinsic index?
				None => return Err("No extrinsic index found.")
			}
		})
	}
}
