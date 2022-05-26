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
use sp_runtime::{
	traits::{BadOrigin, Member},
	Either,
};

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
	/// ** Should be used for benchmarking only!!! **
	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin(a: &Argument) -> OuterOrigin;
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
	fn successful_origin(_: &Argument) -> OuterOrigin {
		EO::successful_origin()
	}
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

/// Type that can be dispatched with an additional storage layer which is used to execute the call.
pub trait DispatchableWithStorageLayer {
	/// The origin type of the runtime, (i.e. `frame_system::Config::Origin`).
	type Origin;

	/// Same as `dispatch` from the [`frame_support::dispatch::Dispatchable`] trait, but
	/// specifically spawns a new storage layer to execute the call inside of.
	fn dispatch_with_storage_layer(self, origin: Self::Origin) -> DispatchResultWithPostInfo;

	/// Same as `dispatch_bypass_filter` from the [`UnfilteredDispatchable`] trait, but specifically
	/// spawns a new storage layer to execute the call inside of.
	fn dispatch_bypass_filter_with_storage_layer(
		self,
		origin: Self::Origin,
	) -> DispatchResultWithPostInfo;
}

/// Methods available on `frame_system::Config::Origin`.
pub trait OriginTrait: Sized {
	/// Runtime call type, as in `frame_system::Config::Call`
	type Call;

	/// The caller origin, overarching type of all pallets origins.
	type PalletsOrigin: Parameter + Member + Into<Self> + From<RawOrigin<Self::AccountId>>;

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

/// The "OR gate" implementation of `EnsureOrigin`.
///
/// Origin check will pass if `L` or `R` origin check passes. `L` is tested first.
pub struct EnsureOneOf<L, R>(sp_std::marker::PhantomData<(L, R)>);

impl<OuterOrigin, L: EnsureOrigin<OuterOrigin>, R: EnsureOrigin<OuterOrigin>>
	EnsureOrigin<OuterOrigin> for EnsureOneOf<L, R>
{
	type Success = Either<L::Success, R::Success>;
	fn try_origin(o: OuterOrigin) -> Result<Self::Success, OuterOrigin> {
		L::try_origin(o)
			.map_or_else(|o| R::try_origin(o).map(Either::Right), |o| Ok(Either::Left(o)))
	}

	#[cfg(feature = "runtime-benchmarks")]
	fn successful_origin() -> OuterOrigin {
		L::successful_origin()
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	struct EnsureSuccess;
	struct EnsureFail;

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

	#[test]
	fn ensure_one_of_test() {
		assert!(<EnsureOneOf<EnsureSuccess, EnsureSuccess>>::try_origin(()).is_ok());
		assert!(<EnsureOneOf<EnsureSuccess, EnsureFail>>::try_origin(()).is_ok());
		assert!(<EnsureOneOf<EnsureFail, EnsureSuccess>>::try_origin(()).is_ok());
		assert!(<EnsureOneOf<EnsureFail, EnsureFail>>::try_origin(()).is_err());
	}
}
