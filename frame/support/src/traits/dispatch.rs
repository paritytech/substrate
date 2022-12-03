// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Traits for dealing with dispatching calls and the origin from which they are dispatched.

use crate::dispatch::{DispatchResultWithPostInfo, Parameter, RawOrigin};
use codec::MaxEncodedLen;
use sp_runtime::{
	traits::{BadOrigin, Member, Morph, TryMorph},
	Either,
};
use sp_std::marker::PhantomData;

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOrigin<OuterOrigin> {
	/// A return type.
	type Success;

	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin) -> Result<Self::Success, BadOrigin> {
		Self::try_origin(o).map_err(|_| BadOrigin)
	}

	/// Perform the origin check.
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin>;

	/// Returns an outer origin capable of passing `try_origin` check.
	///
	/// NOTE: This should generally *NOT* be reimplemented. Instead implement
	/// `try_successful_origin`.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin {
		Self::try_successful_origin().expect("No origin exists which can satisfy the guard")
	}

	/// Attept to get an outer origin capable of passing `try_origin` check. May return `Err` if it
	/// is impossible. Default implementation just uses `successful_origin()`.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OuterOrigin, ()> {
		Ok(Self::successful_origin())
	}
}

/// `EnsureOrigin` implementation that always fails.
pub struct NeverEnsureOrigin<Success>(sp_std::marker::PhantomData<Success>);
impl<OO, Success> EnsureOrigin<OO> for NeverEnsureOrigin<Success> {
	type Success = Success;
	fn try_origin(o: OO) -> Result<Success, OO> {
		Err(o)
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OO, ()> {
		Err(())
	}
}

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOriginWithArg<OuterOrigin, Argument> {
	/// A return type.
	type Success;

	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin, a: &Argument) -> Result<Self::Success, BadOrigin> {
		Self::try_origin(o, a).map_err(|_| BadOrigin)
	}

	/// Perform the origin check, returning the origin value if unsuccessful. This allows chaining.
	fn try_origin(o: OuterOrigin, a: &Argument) -> Result<Self::Success, OuterOrigin>;

	/// Returns an outer origin capable of passing `try_origin` check.
	///
	/// NOTE: This should generally *NOT* be reimplemented. Instead implement
	/// `try_successful_origin`.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin(a: &Argument) -> OuterOrigin {
		Self::try_successful_origin(a).expect("No origin exists which can satisfy the guard")
	}

	/// Attept to get an outer origin capable of passing `try_origin` check. May return `Err` if it
	/// is impossible. Default implementation just uses `successful_origin()`.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &Argument) -> Result<OuterOrigin, ()> {
		Ok(Self::successful_origin(a))
	}
}

pub struct AsEnsureOriginWithArg<EO>(sp_std::marker::PhantomData<EO>);
impl<OuterOrigin, Argument, EO: EnsureOrigin<OuterOrigin>>
	EnsureOriginWithArg<OuterOrigin, Argument> for AsEnsureOriginWithArg<EO>
{
	/// A return type.
	type Success = EO::Success;

	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin, _: &Argument) -> Result<Self::Success, BadOrigin> {
		EO::ensure_origin(o)
	}

	/// Perform the origin check, returning the origin value if unsuccessful. This allows chaining.
	fn try_origin(o: OuterOrigin, _: &Argument) -> Result<Self::Success, OuterOrigin> {
		EO::try_origin(o)
	}

	/// Returns an outer origin capable of passing `try_origin` check.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(_: &Argument) -> Result<OuterOrigin, ()> {
		EO::try_successful_origin()
	}
}

/// A derivative `EnsureOrigin` implementation. It mutates the `Success` result of an `Original`
/// implementation with a given `Mutator`.
pub struct MapSuccess<Original, Mutator>(PhantomData<(Original, Mutator)>);
impl<O, Original: EnsureOrigin<O>, Mutator: Morph<Original::Success>> EnsureOrigin<O>
	for MapSuccess<Original, Mutator>
{
	type Success = Mutator::Outcome;
	fn try_origin(o: O) -> Result<Mutator::Outcome, O> {
		Ok(Mutator::morph(Original::try_origin(o)?))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Original::try_successful_origin()
	}
}

/// A derivative `EnsureOrigin` implementation. It mutates the `Success` result of an `Original`
/// implementation with a given `Mutator`, allowing the possibility of an error to be returned
/// from the mutator.
///
/// NOTE: This is strictly worse performance than `MapSuccess` since it clones the original origin
/// value. If possible, use `MapSuccess` instead.
pub struct TryMapSuccess<Orig, Mutator>(PhantomData<(Orig, Mutator)>);
impl<O: Clone, Original: EnsureOrigin<O>, Mutator: TryMorph<Original::Success>> EnsureOrigin<O>
	for TryMapSuccess<Original, Mutator>
{
	type Success = Mutator::Outcome;
	fn try_origin(o: O) -> Result<Mutator::Outcome, O> {
		let orig = o.clone();
		Mutator::try_morph(Original::try_origin(o)?).map_err(|()| orig)
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<O, ()> {
		Original::try_successful_origin()
	}
}

/// "OR gate" implementation of `EnsureOrigin` allowing for different `Success` types for `L`
/// and `R`, with them combined using an `Either` type.
///
/// Origin check will pass if `L` or `R` origin check passes. `L` is tested first.
///
/// Successful origin is derived from the left side.
pub struct EitherOfDiverse<L, R>(sp_std::marker::PhantomData<(L, R)>);
impl<OuterOrigin, L: EnsureOrigin<OuterOrigin>, R: EnsureOrigin<OuterOrigin>>
	EnsureOrigin<OuterOrigin> for EitherOfDiverse<L, R>
{
	type Success = Either<L::Success, R::Success>;
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o)
			.map_or_else(|o| R::try_origin(o).map(Either::Right), |o| Ok(Either::Left(o)))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OuterOrigin, ()> {
		L::try_successful_origin().or_else(|()| R::try_successful_origin())
	}
}

/// "OR gate" implementation of `EnsureOrigin` allowing for different `Success` types for `L`
/// and `R`, with them combined using an `Either` type.
///
/// Origin check will pass if `L` or `R` origin check passes. `L` is tested first.
///
/// Successful origin is derived from the left side.
#[deprecated = "Use `EitherOfDiverse` instead"]
pub type EnsureOneOf<L, R> = EitherOfDiverse<L, R>;

/// "OR gate" implementation of `EnsureOrigin`, `Success` type for both `L` and `R` must
/// be equal.
///
/// Origin check will pass if `L` or `R` origin check passes. `L` is tested first.
///
/// Successful origin is derived from the left side.
pub struct EitherOf<L, R>(sp_std::marker::PhantomData<(L, R)>);
impl<
		OuterOrigin,
		L: EnsureOrigin<OuterOrigin>,
		R: EnsureOrigin<OuterOrigin, Success = L::Success>,
	> EnsureOrigin<OuterOrigin> for EitherOf<L, R>
{
	type Success = L::Success;
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o).or_else(|o| R::try_origin(o))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OuterOrigin, ()> {
		L::try_successful_origin().or_else(|()| R::try_successful_origin())
	}
}

/// Type that can be dispatched with an origin but without checking the origin filter.
///
/// Implemented for pallet dispatchable type by `decl_module` and for runtime dispatchable by
/// `construct_runtime`.
pub trait UnfilteredDispatchable {
	/// The origin type of the runtime, (i.e. `frame_system::Config::RuntimeOrigin`).
	type RuntimeOrigin;

	/// Dispatch this call but do not check the filter in origin.
	fn dispatch_bypass_filter(self, origin: Self::RuntimeOrigin) -> DispatchResultWithPostInfo;
}

/// The trait implemented by the overarching enumeration of the different pallets' origins.
/// Unlike `OriginTrait` impls, this does not include any kind of dispatch/call filter. Also, this
/// trait is more flexible in terms of how it can be used: it is a `Parameter` and `Member`, so it
/// can be used as dispatchable parameters as well as in storage items.
pub trait CallerTrait<AccountId>: Parameter + Member + From<RawOrigin<AccountId>> {
	/// Extract the signer from the message if it is a `Signed` origin.
	fn into_system(self) -> Option<RawOrigin<AccountId>>;

	/// Extract a reference to the system-level `RawOrigin` if it is that.
	fn as_system_ref(&self) -> Option<&RawOrigin<AccountId>>;
}

/// Methods available on `frame_system::Config::RuntimeOrigin`.
pub trait OriginTrait: Sized {
	/// Runtime call type, as in `frame_system::Config::Call`
	type Call;

	/// The caller origin, overarching type of all pallets origins.
	type PalletsOrigin: Into<Self> + CallerTrait<Self::AccountId> + MaxEncodedLen;

	/// The AccountId used across the system.
	type AccountId;

	/// Add a filter to the origin.
	fn add_filter(&mut self, filter: impl Fn(&Self::Call) -> bool + 'static);

	/// Reset origin filters to default one, i.e `frame_system::Config::BaseCallFilter`.
	fn reset_filter(&mut self);

	/// Replace the caller with caller from the other origin
	fn set_caller_from(&mut self, other: impl Into<Self>);

	/// Filter the call if caller is not root, if false is returned then the call must be filtered
	/// out.
	///
	/// For root origin caller, the filters are bypassed and true is returned.
	fn filter_call(&self, call: &Self::Call) -> bool;

	/// Get a reference to the caller (`CallerTrait` impl).
	fn caller(&self) -> &Self::PalletsOrigin;

	/// Consume `self` and return the caller.
	fn into_caller(self) -> Self::PalletsOrigin;

	/// Do something with the caller, consuming self but returning it if the caller was unused.
	fn try_with_caller<R>(
		self,
		f: impl FnOnce(Self::PalletsOrigin) -> Result<R, Self::PalletsOrigin>,
	) -> Result<R, Self>;

	/// Create with system none origin and `frame_system::Config::BaseCallFilter`.
	fn none() -> Self;

	/// Create with system root origin and `frame_system::Config::BaseCallFilter`.
	fn root() -> Self;

	/// Create with system signed origin and `frame_system::Config::BaseCallFilter`.
	fn signed(by: Self::AccountId) -> Self;

	/// Extract the signer from the message if it is a `Signed` origin.
	fn as_signed(self) -> Option<Self::AccountId> {
		self.into_caller().into_system().and_then(|s| {
			if let RawOrigin::Signed(who) = s {
				Some(who)
			} else {
				None
			}
		})
	}

	/// Extract a reference to the sytsem origin, if that's what the caller is.
	fn as_system_ref(&self) -> Option<&RawOrigin<Self::AccountId>> {
		self.caller().as_system_ref()
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::traits::{ConstBool, ConstU8, TypedGet};
	use std::marker::PhantomData;

	struct EnsureSuccess<V>(PhantomData<V>);
	struct EnsureFail<T>(PhantomData<T>);

	impl<V: TypedGet> EnsureOrigin<()> for EnsureSuccess<V> {
		type Success = V::Type;
		fn try_origin(_: ()) -> Result<Self::Success, ()> {
			Ok(V::get())
		}
		#[cfg(feature = "runtime-benchmarks")]
		fn try_successful_origin() -> Result<(), ()> {
			Ok(())
		}
	}

	impl<T> EnsureOrigin<()> for EnsureFail<T> {
		type Success = T;
		fn try_origin(_: ()) -> Result<Self::Success, ()> {
			Err(())
		}
		#[cfg(feature = "runtime-benchmarks")]
		fn try_successful_origin() -> Result<(), ()> {
			Err(())
		}
	}

	#[test]
	fn either_of_diverse_works() {
		assert_eq!(
			EitherOfDiverse::<
				EnsureSuccess<ConstBool<true>>,
				EnsureSuccess<ConstU8<0>>,
			>::try_origin(()).unwrap().left(),
			Some(true)
		);
		assert_eq!(
			EitherOfDiverse::<EnsureSuccess<ConstBool<true>>, EnsureFail<u8>>::try_origin(())
				.unwrap()
				.left(),
			Some(true)
		);
		assert_eq!(
			EitherOfDiverse::<EnsureFail<bool>, EnsureSuccess<ConstU8<0>>>::try_origin(())
				.unwrap()
				.right(),
			Some(0u8)
		);
		assert!(EitherOfDiverse::<EnsureFail<bool>, EnsureFail<u8>>::try_origin(()).is_err());
	}

	#[test]
	fn either_of_works() {
		assert_eq!(
			EitherOf::<
				EnsureSuccess<ConstBool<true>>,
				EnsureSuccess<ConstBool<false>>,
			>::try_origin(()).unwrap(),
			true
		);
		assert_eq!(
			EitherOf::<EnsureSuccess<ConstBool<true>>, EnsureFail<bool>>::try_origin(()).unwrap(),
			true
		);
		assert_eq!(
			EitherOf::<EnsureFail<bool>, EnsureSuccess<ConstBool<false>>>::try_origin(()).unwrap(),
			false
		);
		assert!(EitherOf::<EnsureFail<bool>, EnsureFail<bool>>::try_origin(()).is_err());
	}
}
