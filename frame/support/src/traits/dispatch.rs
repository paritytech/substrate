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
use sp_runtime::traits::BadOrigin;

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
/// `construct_runtime` and `impl_outer_dispatch`.
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

	/// Filter the call, if false then call is filtered out.
	fn filter_call(&self, call: &Self::Call) -> bool;

	/// Get the caller.
	fn caller(&self) -> &Self::PalletsOrigin;

	/// Do something with the caller, consuming self but returning it if the caller was unused.
	fn try_with_caller<R>(
		self,
		f: impl FnOnce(Self::PalletsOrigin) -> Result<R, Self::PalletsOrigin>,
	) -> Result<R, Self>;

	/// Create with system none origin and `frame-system::Config::BaseCallFilter`.
	fn none() -> Self;

	/// Create with system root origin and no filter.
	fn root() -> Self;

	/// Create with system signed origin and `frame-system::Config::BaseCallFilter`.
	fn signed(by: Self::AccountId) -> Self;
}
