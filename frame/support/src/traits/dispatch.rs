// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

use crate::dispatch::DispatchResultWithPostInfo;
use sp_runtime::{traits::BadOrigin, Either};

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
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin;
}

/// Type that can be dispatched with an origin but without checking the origin filter.
///
/// Implemented for pallet dispatchable type by `decl_module` and for runtime dispatchable by
/// `construct_runtime`.
pub trait UnfilteredDispatchable {
	/// The origin type of the runtime, (i.e. `frame_system::Config::Origin`).
	type Origin;

	/// Dispatch this call but do not check the filter in origin.
	fn dispatch_bypass_filter(self, origin: Self::Origin) -> DispatchResultWithPostInfo;
}

/// Methods available on `frame_system::Config::Origin`.
pub trait OriginTrait: Sized {
	/// Runtime call type, as in `frame_system::Config::Call`
	type Call;

	/// The caller origin, overarching type of all pallets origins.
	type PalletsOrigin;

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

	/// Get the caller.
	fn caller(&self) -> &Self::PalletsOrigin;

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
}

/// The "OR gate" implementation of `EnsureOrigin` from the same origin.
///
/// Origin check will pass if `L` or `R` origin check passes from the same origin. `L` is tested
/// first.
pub struct EnsureOneOfSameOrigin<L, R>(sp_std::marker::PhantomData<(L, R)>);

impl<OuterOrigin, L: EnsureOrigin<OuterOrigin>, R: EnsureOrigin<OuterOrigin>>
	EnsureOrigin<OuterOrigin> for EnsureOneOfSameOrigin<L, R>
{
	type Success = Either<L::Success, R::Success>;
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o)
			.map_or_else(|o| R::try_origin(o).map(|o| Either::Right(o)), |o| Ok(Either::Left(o)))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin {
		L::successful_origin()
	}
}

/// The "OR gate" implementation of `EnsureOrigin` from the different origins.
///
/// Origin check will pass if `L` or `R` origin check passes from the different origins. `L` is
/// tested first.
pub struct EnsureOneOfDifferentOrigins<L, R>(sp_std::marker::PhantomData<(L, R)>);

impl<OuterOrigin1, OuterOrigin2, L: EnsureOrigin<OuterOrigin1>, R: EnsureOrigin<OuterOrigin2>>
	EnsureOrigin<(OuterOrigin1, OuterOrigin2)> for EnsureOneOfDifferentOrigins<L, R>
{
	type Success = Either<L::Success, R::Success>;
	fn try_origin(
		(o1, o2): (OuterOrigin1, OuterOrigin2),
	) -> Result<Self::Success, (OuterOrigin1, OuterOrigin2)> {
		L::try_origin(o1).map_or_else(
			|o1| R::try_origin(o2).map(|r| Either::Right(r)).map_err(|o2| (o1, o2)),
			|l| Ok(Either::Left(l)),
		)
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> (OuterOrigin1, OuterOrigin2) {
		(L::successful_origin(), R::successful_origin())
	}
}

/// The "OR gate" implementation of `EnsureOrigin` from the same origin.
///
/// Origin check will pass if `L` or `R` origin check passes from the same origin. `L` is
/// tested first.
pub struct EnsureBothOfSameOrigin<L, R>(sp_std::marker::PhantomData<(L, R)>);

impl<OuterOrigin: Clone, L: EnsureOrigin<OuterOrigin>, R: EnsureOrigin<OuterOrigin>>
	EnsureOrigin<OuterOrigin> for EnsureBothOfSameOrigin<L, R>
{
	type Success = (L::Success, R::Success);
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o.clone()).map_or_else(|o| Err(o), |l| R::try_origin(o).map(|r| (l, r)))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin {
		/// It is not possible to implement a successful_origin() for any combination of "L" or "R"
		/// types,  so please generate it manually
		unimplemented!()
	}
}

/// The "OR gate" implementation of `EnsureOrigin` from the different origins.
///
/// Origin check will pass if `L` or `R` origin check passes from the different origins. `L` is
/// tested first.
pub struct EnsureBothOfDifferentOrigins<L, R>(sp_std::marker::PhantomData<(L, R)>);

impl<
		OuterOrigin1: Clone,
		OuterOrigin2: Clone,
		L: EnsureOrigin<OuterOrigin1>,
		R: EnsureOrigin<OuterOrigin2>,
	> EnsureOrigin<(OuterOrigin1, OuterOrigin2)> for EnsureBothOfDifferentOrigins<L, R>
{
	type Success = (L::Success, R::Success);
	fn try_origin(
		(o1, o2): (OuterOrigin1, OuterOrigin2),
	) -> Result<Self::Success, (OuterOrigin1, OuterOrigin2)> {
		let l_suc = L::try_origin(o1.clone()).map_err(|o1| (o1, o2.clone()))?;
		let r_suc = R::try_origin(o2).map_err(|o2| (o1, o2))?;
		Ok((l_suc, r_suc))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin {
		(L::successful_origin(), R::successful_origin())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	struct EnsureSuccess;
	struct EnsureFail;

	struct Ensure;

	impl EnsureOrigin<()> for EnsureSuccess {
		type Success = ();
		fn try_origin(_: ()) -> Result<Self::Success, ()> {
			Ok(())
		}
		#[cfg(feature = "runtime-benchmarks")]
		fn successful_origin() -> () {
			()
		}
	}

	impl EnsureOrigin<()> for EnsureFail {
		type Success = ();
		fn try_origin(_: ()) -> Result<Self::Success, ()> {
			Err(())
		}
		#[cfg(feature = "runtime-benchmarks")]
		fn successful_origin() -> () {
			()
		}
	}

	impl EnsureOrigin<bool> for Ensure {
		type Success = ();
		fn try_origin(o: bool) -> Result<Self::Success, bool> {
			if o {
				Ok(())
			} else {
				Err(o)
			}
		}
	}

	#[test]
	fn ensure_one_of_same_origin_test() {
		assert!(<EnsureOneOfSameOrigin<EnsureSuccess, EnsureSuccess>>::try_origin(()).is_ok());
		assert!(<EnsureOneOfSameOrigin<EnsureSuccess, EnsureFail>>::try_origin(()).is_ok());
		assert!(<EnsureOneOfSameOrigin<EnsureFail, EnsureSuccess>>::try_origin(()).is_ok());
		assert!(<EnsureOneOfSameOrigin<EnsureFail, EnsureFail>>::try_origin(()).is_err());
	}

	#[test]
	fn ensure_one_of_different_origins_test() {
		assert!(<EnsureOneOfDifferentOrigins<Ensure, Ensure>>::try_origin((true, true)).is_ok());
		assert!(<EnsureOneOfDifferentOrigins<Ensure, Ensure>>::try_origin((true, false)).is_ok());
		assert!(<EnsureOneOfDifferentOrigins<Ensure, Ensure>>::try_origin((false, true)).is_ok());
		assert!(<EnsureOneOfDifferentOrigins<Ensure, Ensure>>::try_origin((false, false)).is_err());
	}

	#[test]
	fn ensure_both_of_same_origin_test() {
		assert!(<EnsureBothOfSameOrigin<EnsureSuccess, EnsureSuccess>>::try_origin(()).is_ok());
		assert!(<EnsureBothOfSameOrigin<EnsureSuccess, EnsureFail>>::try_origin(()).is_err());
		assert!(<EnsureBothOfSameOrigin<EnsureFail, EnsureSuccess>>::try_origin(()).is_err());
		assert!(<EnsureBothOfSameOrigin<EnsureFail, EnsureFail>>::try_origin(()).is_err());
	}

	#[test]
	fn ensure_both_of_different_origins_test() {
		assert!(<EnsureBothOfDifferentOrigins<Ensure, Ensure>>::try_origin((true, true)).is_ok());
		assert!(<EnsureBothOfDifferentOrigins<Ensure, Ensure>>::try_origin((true, false)).is_err());
		assert!(<EnsureBothOfDifferentOrigins<Ensure, Ensure>>::try_origin((false, true)).is_err());
		assert!(<EnsureBothOfDifferentOrigins<Ensure, Ensure>>::try_origin((false, false)).is_err());
	}
}
