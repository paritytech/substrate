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

//! Traits for dealing with dispatching calls and the origin from which they are dispatched.

use crate::dispatch::{DispatchResultWithPostInfo, Parameter, RawOrigin};
use codec::MaxEncodedLen;
use sp_runtime::{
	traits::{BadOrigin, Get, Member, Morph, TryMorph},
	Either,
};
use sp_std::{cmp::Ordering, marker::PhantomData};

use super::misc;

/// Some sort of check on the origin is performed by this object.
pub trait EnsureOrigin<OuterOrigin> {
	/// A return type.
	type Success;

	/// Perform the origin check.
	fn ensure_origin(o: OuterOrigin) -> Result<Self::Success, BadOrigin> {
		Self::try_origin(o).map_err(|_| BadOrigin)
	}

	/// The same as `ensure_origin` except that Root origin will always pass. This can only be
	/// used if `Success` has a sensible impl of `Default` since that will be used in the result.
	fn ensure_origin_or_root(o: OuterOrigin) -> Result<Option<Self::Success>, BadOrigin>
	where
		OuterOrigin: OriginTrait,
	{
		if o.caller().is_root() {
			return Ok(None)
		} else {
			Self::ensure_origin(o).map(Some)
		}
	}

	/// Perform the origin check.
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin>;

	/// The same as `try_origin` except that Root origin will always pass. This can only be
	/// used if `Success` has a sensible impl of `Default` since that will be used in the result.
	fn try_origin_or_root(o: OuterOrigin) -> Result<Option<Self::Success>, OuterOrigin>
	where
		OuterOrigin: OriginTrait,
	{
		if o.caller().is_root() {
			return Ok(None)
		} else {
			Self::try_origin(o).map(Some)
		}
	}

	/// Attempt to get an outer origin capable of passing `try_origin` check. May return `Err` if it
	/// is impossible.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OuterOrigin, ()>;
}

/// [`EnsureOrigin`] implementation that checks that an origin has equal or higher privilege
/// compared to the expected `Origin`.
///
/// It will take the shortcut of comparing the incoming origin with the expected `Origin` and if
/// both are the same the origin is accepted.
///
/// # Example
///
/// ```rust
/// # use frame_support::traits::{EnsureOriginEqualOrHigherPrivilege, PrivilegeCmp, EnsureOrigin as _};
/// # use sp_runtime::traits::{parameter_types, Get};
/// # use sp_std::cmp::Ordering;
///
/// #[derive(Eq, PartialEq, Debug)]
/// pub enum Origin {
///     Root,
///     SomethingBelowRoot,
///     NormalUser,
/// }
///
/// struct OriginPrivilegeCmp;
///
/// impl PrivilegeCmp<Origin> for OriginPrivilegeCmp {
///     fn cmp_privilege(left: &Origin, right: &Origin) -> Option<Ordering> {
///         match (left, right) {
///             (Origin::Root, Origin::Root) => Some(Ordering::Equal),
///             (Origin::Root, _) => Some(Ordering::Greater),
///             (Origin::SomethingBelowRoot, Origin::SomethingBelowRoot) => Some(Ordering::Equal),
///             (Origin::SomethingBelowRoot, Origin::Root) => Some(Ordering::Less),
///             (Origin::SomethingBelowRoot, Origin::NormalUser) => Some(Ordering::Greater),
///             (Origin::NormalUser, Origin::NormalUser) => Some(Ordering::Equal),
///             (Origin::NormalUser, _) => Some(Ordering::Less),
///         }
///     }
/// }
///
/// parameter_types! {
///     pub const ExpectedOrigin: Origin = Origin::SomethingBelowRoot;
/// }
///
/// type EnsureOrigin = EnsureOriginEqualOrHigherPrivilege<ExpectedOrigin, OriginPrivilegeCmp>;
///
/// // `Root` has an higher privilege as our expected origin.
/// assert!(EnsureOrigin::ensure_origin(Origin::Root).is_ok());
/// // `SomethingBelowRoot` is exactly the expected origin.
/// assert!(EnsureOrigin::ensure_origin(Origin::SomethingBelowRoot).is_ok());
/// // The `NormalUser` origin is not allowed.
/// assert!(EnsureOrigin::ensure_origin(Origin::NormalUser).is_err());
/// ```
pub struct EnsureOriginEqualOrHigherPrivilege<Origin, PrivilegeCmp>(
	sp_std::marker::PhantomData<(Origin, PrivilegeCmp)>,
);

impl<OuterOrigin, Origin, PrivilegeCmp> EnsureOrigin<OuterOrigin>
	for EnsureOriginEqualOrHigherPrivilege<Origin, PrivilegeCmp>
where
	Origin: Get<OuterOrigin>,
	OuterOrigin: Eq,
	PrivilegeCmp: misc::PrivilegeCmp<OuterOrigin>,
{
	type Success = ();

	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		let expected_origin = Origin::get();

		// If this is the expected origin, it has the same privilege.
		if o == expected_origin {
			return Ok(())
		}

		let cmp = PrivilegeCmp::cmp_privilege(&o, &expected_origin);

		match cmp {
			Some(Ordering::Equal) | Some(Ordering::Greater) => Ok(()),
			None | Some(Ordering::Less) => Err(o),
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin() -> Result<OuterOrigin, ()> {
		Ok(Origin::get())
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

	/// Attempt to get an outer origin capable of passing `try_origin` check. May return `Err` if it
	/// is impossible.
	///
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &Argument) -> Result<OuterOrigin, ()>;
}

/// Simple macro to explicitly implement [EnsureOriginWithArg] to be used on any type which
/// implements [EnsureOrigin]. This is quick and dirty, so you must use the type parameters `O`
/// (the origin type), `T` (the argument type) and `AccountId` (if you are using the `O: ..` form).
///
/// The argument is ignored, much like in [AsEnsureOriginWithArg].
#[macro_export]
macro_rules! impl_ensure_origin_with_arg_ignoring_arg {
	( impl < { O: .., I: 'static, $( $bound:tt )* }> EnsureOriginWithArg<O, $t_param:ty> for $name:ty {} ) => {
		impl_ensure_origin_with_arg_ignoring_arg! {
			impl <{
				O: Into<Result<RawOrigin<AccountId, I>, O>> + From<RawOrigin<AccountId, I>>,
				I: 'static,
				$( $bound )*
			}> EnsureOriginWithArg<O, $t_param> for $name {}
		}
	};
	( impl < { O: .. , $( $bound:tt )* }> EnsureOriginWithArg<O, $t_param:ty> for $name:ty {} ) => {
		impl_ensure_origin_with_arg_ignoring_arg! {
			impl <{
				O: Into<Result<RawOrigin<AccountId>, O>> + From<RawOrigin<AccountId>>,
				$( $bound )*
			}> EnsureOriginWithArg<O, $t_param> for $name {}
		}
	};
	( impl < { $( $bound:tt )* } > EnsureOriginWithArg<$o_param:ty, $t_param:ty> for $name:ty {} ) => {
		impl < $( $bound )* > EnsureOriginWithArg<$o_param, $t_param> for $name {
			type Success = <Self as EnsureOrigin<$o_param>>::Success;
			fn try_origin(o: $o_param, _: &$t_param) -> Result<Self::Success, $o_param> {
				<Self as EnsureOrigin<$o_param>>::try_origin(o)
			}
			#[cfg(feature = "runtime-benchmarks")]
			fn try_successful_origin(_: &$t_param) -> Result<$o_param, ()> {
				<Self as EnsureOrigin<$o_param>>::try_successful_origin()
			}
		}
	}
}

/// [`EnsureOrigin`] implementation that always fails.
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
impl_ensure_origin_with_arg_ignoring_arg! {
	impl<{ OO, Success, A }>
		EnsureOriginWithArg<OO, A> for NeverEnsureOrigin<Success>
	{}
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
impl<O, Original: EnsureOriginWithArg<O, A>, Mutator: Morph<Original::Success>, A>
	EnsureOriginWithArg<O, A> for MapSuccess<Original, Mutator>
{
	type Success = Mutator::Outcome;
	fn try_origin(o: O, a: &A) -> Result<Mutator::Outcome, O> {
		Ok(Mutator::morph(Original::try_origin(o, a)?))
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &A) -> Result<O, ()> {
		Original::try_successful_origin(a)
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
impl<O: Clone, Original: EnsureOriginWithArg<O, A>, Mutator: TryMorph<Original::Success>, A>
	EnsureOriginWithArg<O, A> for TryMapSuccess<Original, Mutator>
{
	type Success = Mutator::Outcome;
	fn try_origin(o: O, a: &A) -> Result<Mutator::Outcome, O> {
		let orig = o.clone();
		Mutator::try_morph(Original::try_origin(o, a)?).map_err(|()| orig)
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &A) -> Result<O, ()> {
		Original::try_successful_origin(a)
	}
}

pub struct TryWithMorphedArg<O, A, Morph, Inner, Success>(
	PhantomData<(O, A, Morph, Inner, Success)>,
);
impl<
		O,
		A,
		Morph: for<'a> TryMorph<&'a A>,
		Inner: for<'a> EnsureOriginWithArg<O, <Morph as TryMorph<&'a A>>::Outcome, Success = Success>,
		Success,
	> EnsureOriginWithArg<O, A> for TryWithMorphedArg<O, A, Morph, Inner, Success>
{
	type Success = Success;
	fn try_origin(o: O, a: &A) -> Result<Success, O> {
		match Morph::try_morph(a) {
			Ok(x) => Inner::try_origin(o, &x),
			_ => return Err(o),
		}
	}
	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &A) -> Result<O, ()> {
		Inner::try_successful_origin(&Morph::try_morph(a).map_err(|_| ())?)
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
impl<
		OuterOrigin,
		L: EnsureOriginWithArg<OuterOrigin, Argument>,
		R: EnsureOriginWithArg<OuterOrigin, Argument>,
		Argument,
	> EnsureOriginWithArg<OuterOrigin, Argument> for EitherOfDiverse<L, R>
{
	type Success = Either<L::Success, R::Success>;
	fn try_origin(o: OuterOrigin, a: &Argument) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o, a)
			.map_or_else(|o| R::try_origin(o, a).map(Either::Right), |o| Ok(Either::Left(o)))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &Argument) -> Result<OuterOrigin, ()> {
		L::try_successful_origin(a).or_else(|()| R::try_successful_origin(a))
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
impl<
		OuterOrigin,
		L: EnsureOriginWithArg<OuterOrigin, Argument>,
		R: EnsureOriginWithArg<OuterOrigin, Argument, Success = L::Success>,
		Argument,
	> EnsureOriginWithArg<OuterOrigin, Argument> for EitherOf<L, R>
{
	type Success = L::Success;
	fn try_origin(o: OuterOrigin, a: &Argument) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o, a).or_else(|o| R::try_origin(o, a))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn try_successful_origin(a: &Argument) -> Result<OuterOrigin, ()> {
		L::try_successful_origin(a).or_else(|()| R::try_successful_origin(a))
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

	/// Extract the signer from it if a system `Signed` origin, `None` otherwise.
	fn as_signed(&self) -> Option<&AccountId> {
		self.as_system_ref().and_then(RawOrigin::as_signed)
	}

	/// Returns `true` if `self` is a system `Root` origin, `None` otherwise.
	fn is_root(&self) -> bool {
		self.as_system_ref().map_or(false, RawOrigin::is_root)
	}

	/// Returns `true` if `self` is a system `None` origin, `None` otherwise.
	fn is_none(&self) -> bool {
		self.as_system_ref().map_or(false, RawOrigin::is_none)
	}
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
	#[deprecated = "Use `into_signer` instead"]
	fn as_signed(self) -> Option<Self::AccountId> {
		self.into_signer()
	}

	/// Extract the signer from the message if it is a `Signed` origin.
	fn into_signer(self) -> Option<Self::AccountId> {
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
