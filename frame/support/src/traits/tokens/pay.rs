// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! The Pay trait and associated types.

use codec::{Decode, Encode, FullCodec, MaxEncodedLen};
use scale_info::TypeInfo;
use sp_core::{RuntimeDebug, TypedGet};
use sp_std::fmt::Debug;

use super::{fungible, Balance, Preservation::Expendable};

/// Can be implemented by `PayFromAccount` using a `fungible` impl, but can also be implemented with
/// XCM/MultiAsset and made generic over assets.
pub trait Pay {
	/// The type by which we measure units of the currency in which we make payments.
	type Balance: Balance;
	/// The type by which we identify the beneficiaries to whom a payment may be made.
	type Beneficiary;
	/// The type for the kinds of asset that are going to be paid.
	///
	/// The unit type can be used here to indicate there's only one kind of asset to do payments
	/// with. When implementing, it should be clear from the context what that asset is.
	type AssetKind;
	/// An identifier given to an individual payment.
	type Id: FullCodec + MaxEncodedLen + TypeInfo + Clone + Eq + PartialEq + Debug + Copy;
	/// Make a payment and return an identifier for later evaluation of success in some off-chain
	/// mechanism (likely an event, but possibly not on this chain).
	fn pay(
		who: &Self::Beneficiary,
		asset_kind: Self::AssetKind,
		amount: Self::Balance,
	) -> Result<Self::Id, ()>;
	/// Check how a payment has proceeded. `id` must have been previously returned by `pay` for
	/// the result of this call to be meaningful. Once this returns anything other than
	/// `InProgress` for some `id` it must return `Unknown` rather than the actual result
	/// value.
	fn check_payment(id: Self::Id) -> PaymentStatus;
	/// Ensure that a call to pay with the given parameters will be successful if done immediately
	/// after this call. Used in benchmarking code.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(who: &Self::Beneficiary, amount: Self::Balance);
	/// Ensure that a call to `check_payment` with the given parameters will return either `Success`
	/// or `Failure`.
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(id: Self::Id);
}

/// Status for making a payment via the `Pay::pay` trait function.
#[derive(Encode, Decode, Eq, PartialEq, Clone, TypeInfo, MaxEncodedLen, RuntimeDebug)]
pub enum PaymentStatus {
	/// Payment is in progress. Nothing to report yet.
	InProgress,
	/// Payment status is unknowable. It may already have reported the result, or if not then
	/// it will never be reported successful or failed.
	Unknown,
	/// Payment happened successfully.
	Success,
	/// Payment failed. It may safely be retried.
	Failure,
}

/// Simple implementation of `Pay` which makes a payment from a "pot" - i.e. a single account.
pub struct PayFromAccount<F, A>(sp_std::marker::PhantomData<(F, A)>);
impl<A: TypedGet, F: fungible::Mutate<A::Type>> Pay for PayFromAccount<F, A> {
	type Balance = F::Balance;
	type Beneficiary = A::Type;
	type AssetKind = ();
	type Id = ();
	fn pay(
		who: &Self::Beneficiary,
		_: Self::AssetKind,
		amount: Self::Balance,
	) -> Result<Self::Id, ()> {
		<F as fungible::Mutate<_>>::transfer(&A::get(), who, amount, Expendable).map_err(|_| ())?;
		Ok(())
	}
	fn check_payment(_: ()) -> PaymentStatus {
		PaymentStatus::Success
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_successful(_: &Self::Beneficiary, amount: Self::Balance) {
		<F as fungible::Mutate<_>>::mint_into(&A::get(), amount).unwrap();
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn ensure_concluded(_: Self::Id) {}
}
