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
//! Hence, the primitives that this module uses to _charge an inclusion payment_ from the dispatch
//! origin are rather simple and static (as opposed to dynamic and complicated systems like gas
//! metering).
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
use codec::{Codec, Encode, Decode};
use support::{
	StorageValue, Parameter, decl_event, decl_storage, decl_module,
	traits::{Currency, Get},
	dispatch::Result,
};
use sr_primitives::{
	transaction_validity::{
		TransactionPriority, ValidTransaction, InvalidTransaction, TransactionValidityError,
		TransactionValidity,
	},
	traits::{
		Zero, SimpleArithmetic, StaticLookup, Member, CheckedAdd, CheckedSub, MaybeSerializeDebug,
		Saturating, Bounded, SignedExtension, SaturatedConversion, Convert,
	},
	weights::Weight,
};
use system::{IsDeadAccount, OnNewAccount, ensure_signed, ensure_root};


// Imagine this going into support.
/// Something that can convert a weight type into a _deductible currency_.
pub trait WeightToFee<B> {
	fn weight_to_fee(w: Weight) -> B;
}

impl<B: Zero> WeightToFee<B> for () {
	fn weight_to_fee(_: Weight) -> B {
		Zero::zero()
	}
}

pub type BalanceOf<T> =
	<<T as Trait>::Currency as Currency<<T as system::Trait>::AccountId>>::Balance;

pub trait Trait: system::Trait {
	/// The currency type of the chain.
	type Currency: Currency<Self::AccountId> + Codec;

	/// The fee to be paid for making a transaction; the base.
	type TransactionBaseFee: Get<Self::Currency>;

	/// The fee to be paid for making a transaction; the per-byte portion.
	type TransactionByteFee: Get<Self::Currency>;
}

decl_storage! {
	trait Store for Module<T: Trait> as Balances {

	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The fee to be paid for making a transaction; the base.
		const TransactionBaseFee: T::Currency = T::TransactionBaseFee::get();

		/// The fee to be paid for making a transaction; the per-byte portion.
		const TransactionByteFee: T::Currency = T::TransactionByteFee::get();

		// user dispatchables? nada.
	}
}

impl<T: Trait> Module<T> {}

impl<T: Trait> WeightToFee<BalanceOf<T>> for Module<T> {
	fn weight_to_fee(w: Weight) -> BalanceOf<T> {
		// assume this module implements a simple multiplier
		Zero::zero()
	}
}
