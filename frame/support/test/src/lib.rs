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

//! Minimal pallet without `frame_system::Config`-super trait.

// Make sure we fail compilation on warnings
#![warn(missing_docs)]
#![deny(warnings)]

pub use frame_support::dispatch::RawOrigin;
use frame_system::pallet_prelude::BlockNumberFor;

pub use self::pallet::*;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use crate::{self as frame_system, pallet_prelude::*};
	use frame_support::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// The configuration trait.
	#[pallet::config]
	#[pallet::disable_frame_system_supertrait_check]
	pub trait Config: 'static + Eq + Clone {
		/// The block number type.
		type BlockNumber: Parameter + Member + Default + MaybeSerializeDeserialize + MaxEncodedLen;
		/// The account type.
		type AccountId: Parameter + Member + MaxEncodedLen;
		/// The basic call filter to use in Origin.
		type BaseCallFilter: frame_support::traits::Contains<Self::RuntimeCall>;
		/// The runtime origin type.
		type RuntimeOrigin: Into<Result<RawOrigin<Self::AccountId>, Self::RuntimeOrigin>>
			+ From<RawOrigin<Self::AccountId>>;
		/// The runtime call type.
		type RuntimeCall;
		/// The runtime event type.
		type RuntimeEvent: Parameter
			+ Member
			+ IsType<<Self as frame_system::Config>::RuntimeEvent>
			+ From<Event<Self>>;
		/// The information about the pallet setup in the runtime.
		type PalletInfo: frame_support::traits::PalletInfo;
		/// The db weights.
		type DbWeight: Get<frame_support::weights::RuntimeDbWeight>;
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// A noop call.
		pub fn noop(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}

	impl<T: Config> Pallet<T> {
		/// A empty method.
		pub fn deposit_event(_event: impl Into<T::RuntimeEvent>) {}
	}

	/// The origin type.
	#[pallet::origin]
	pub type Origin<T> = RawOrigin<<T as Config>::AccountId>;

	/// The error type.
	#[pallet::error]
	pub enum Error<T> {
		/// Test error documentation
		TestError,
		/// Error documentation
		/// with multiple lines
		AnotherError,
		/// Required by construct_runtime
		CallFiltered,
	}

	/// The event type.
	#[pallet::event]
	pub enum Event<T: Config> {
		/// The extrinsic is successful
		ExtrinsicSuccess,
		/// The extrinsic is failed
		ExtrinsicFailed,
		/// The ignored error
		Ignore(<T as Config>::BlockNumber),
	}
}

/// Ensure that the origin `o` represents the root. Returns `Ok` or an `Err` otherwise.
pub fn ensure_root<OuterOrigin, AccountId>(o: OuterOrigin) -> Result<(), &'static str>
where
	OuterOrigin: Into<Result<RawOrigin<AccountId>, OuterOrigin>>,
{
	o.into().map(|_| ()).map_err(|_| "bad origin: expected to be a root origin")
}

/// Same semantic as [`frame_system`].
// Note: we cannot use [`frame_system`] here since the pallet does not depend on
// [`frame_system::Config`].
pub mod pallet_prelude {
	pub use crate::ensure_root;

	/// Type alias for the `Origin` associated type of system config.
	pub type OriginFor<T> = <T as crate::Config>::RuntimeOrigin;

	/// Type alias for the `BlockNumber` associated type of system config.
	pub type BlockNumberFor<T> = <T as super::Config>::BlockNumber;
}

/// Provides an implementation of [`frame_support::traits::Randomness`] that should only be used in
/// tests!
pub struct TestRandomness<T>(sp_std::marker::PhantomData<T>);

impl<Output: codec::Decode + Default, T>
	frame_support::traits::Randomness<Output, BlockNumberFor<T>> for TestRandomness<T>
where
	T: frame_system::Config,
{
	fn random(subject: &[u8]) -> (Output, BlockNumberFor<T>) {
		use sp_runtime::traits::TrailingZeroInput;

		(
			Output::decode(&mut TrailingZeroInput::new(subject)).unwrap_or_default(),
			frame_system::Pallet::<T>::block_number(),
		)
	}
}
