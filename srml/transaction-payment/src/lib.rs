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

//! # Transaction Payment Module
//!
//! This module provides the logic needed to approve that a transaction is paying the _absolute
//! minimum_ amount required to be included on-chain. Note that this is similar, but by no means the
//! same as what a typical blockchain system names _transaction fee_. Substrate makes no assumption
//! about the type of the transactions, ergo no assumption is also made about the existence of a
//! fee.
//!
//!
//!
//!

// The way that it should work is that the system module assumes that the concept of weight is fixed
// it will try and use an external module to estimate how mcuh fee does a weigth number correspond to.
// so in the long term I suspect the TakeFee to actully go into the system module (maybe also here but)
// the rational is that the weight system os **mandatory**.

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use codec::{Encode, Decode};
use support::{
	decl_storage, decl_module,
	traits::{Currency, Get, OnUnbalanced, ExistenceRequirement, WithdrawReason},
};
use sr_primitives::{
	Fixed64,
	transaction_validity::{
		TransactionPriority, ValidTransaction, InvalidTransaction, TransactionValidityError,
		TransactionValidity,
	},
	traits::{Zero, Saturating, SignedExtension, SaturatedConversion, Convert},
	weights::{Weight, DispatchInfo},
};

type Multiplier = Fixed64;
pub type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;
pub type NegativeImbalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::NegativeImbalance;

pub trait Trait: system::Trait {
	/// The currency type of the chain.
	type Currency: Currency<Self::AccountId>;

	/// Handler for the unbalanced reduction when taking transaction fees.
	type OnTransactionPayment: OnUnbalanced<NegativeImbalanceOf<Self>>;

	/// The fee to be paid for making a transaction; the base.
	type TransactionBaseFee: Get<BalanceOf<Self>>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee: Get<BalanceOf<Self>>;

	/// Convert a weight value into a deductible fee based on the currency type.
	type WeightToFee: Convert<Weight, BalanceOf<Self>>;

	/// Update the multiplier of the next block, based on the previous block's weight.
	// TODO: maybe this does not need previous weight and can just read it
	type FeeMultiplierUpdate: Convert<(Weight, Multiplier), Multiplier>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Balances {
		NextFeeMultiplier get(next_fee_multiplier): Multiplier = Multiplier::one();
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The fee to be paid for making a transaction; the base.
		const TransactionBaseFee: BalanceOf<T> = T::TransactionBaseFee::get();

		/// The fee to be paid for making a transaction; the per-byte portion.
		const TransactionByteFee: BalanceOf<T> = T::TransactionByteFee::get();

		fn on_finalize() {
			let current_weight = <system::Module<T>>::all_extrinsics_weight();
			NextFeeMultiplier::mutate(|fm| {
				*fm = T::FeeMultiplierUpdate::convert((current_weight, *fm))
			});
		}
	}
}

impl<T: Trait> Module<T> {}

/// Require the transactor pay for themselves and maybe include a tip to gain additional priority
/// in the queue.
#[derive(Encode, Decode, Clone, Eq, PartialEq)]
pub struct ChargeTransactionPayment<T: Trait>(#[codec(compact)] BalanceOf<T>);

impl<T: Trait> ChargeTransactionPayment<T> {
	/// utility constructor. Used only in client/factory code.
	pub fn from(fee: BalanceOf<T>) -> Self {
		Self(fee)
	}

	/// Compute the final fee value for a particular transaction.
	///
	/// The final fee is composed of:
	///   - _length-fee_: This is the amount paid merely to pay for size of the transaction.
	///   - _weight-fee_: This amount is computed based on the weight of the transaction. Unlike
	///      size-fee, this is not input dependent and reflects the _complexity_ of the execution
	///      and the time it consumes.
	///   - (optional) _tip_: if included in the transaction, it will be added on top. Only signed
	///      transactions can have a tip.
	fn compute_fee(len: usize, info: DispatchInfo, tip: BalanceOf<T>) -> BalanceOf<T> {
		let len_fee = if info.pay_length_fee() {
			let len = <BalanceOf<T>>::from(len as u32);
			let base = T::TransactionBaseFee::get();
			let per_byte = T::TransactionByteFee::get();
			base.saturating_add(per_byte.saturating_mul(len))
		} else {
			Zero::zero()
		};

		let weight_fee = {
			// cap the weight to the maximum defined in runtime, otherwise it will be the `Bounded`
			// maximum of its data type, which is not desired.
			let capped_weight = info.weight.min(<T as system::Trait>::MaximumBlockWeight::get());
			let fee = T::WeightToFee::convert(capped_weight);
			let fee_update = NextFeeMultiplier::get();
			let adjusted_fee = fee_update.saturated_multiply_accumulate(fee);
			adjusted_fee
		};

		len_fee.saturating_add(weight_fee).saturating_add(tip)
	}
}

#[cfg(feature = "std")]
impl<T: Trait> rstd::fmt::Debug for ChargeTransactionPayment<T> {
	fn fmt(&self, f: &mut rstd::fmt::Formatter) -> rstd::fmt::Result {
		self.0.fmt(f)
	}
}

impl<T: Trait> SignedExtension for ChargeTransactionPayment<T> where BalanceOf<T>: Send + Sync {
	type AccountId = T::AccountId;
	type Call = T::Call;
	type AdditionalSigned = ();
	type Pre = ();
	fn additional_signed(&self) -> rstd::result::Result<(), TransactionValidityError> { Ok(()) }

	fn validate(
		&self,
		who: &Self::AccountId,
		_call: &Self::Call,
		info: DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		// pay any fees.
		let fee = Self::compute_fee(len, info, self.0);
		let imbalance = match T::Currency::withdraw(
			who,
			fee,
			WithdrawReason::TransactionPayment,
			ExistenceRequirement::KeepAlive,
		) {
			Ok(imbalance) => imbalance,
			Err(_) => return InvalidTransaction::Payment.into(),
		};
		T::OnTransactionPayment::on_unbalanced(imbalance);

		let mut r = ValidTransaction::default();
		// NOTE: we probably want to maximize the _fee (of any type) per weight unit_ here, which
		// will be a bit more than setting the priority to tip. For now, this is enough.
		r.priority = fee.saturated_into::<TransactionPriority>();
		Ok(r)
	}
}

