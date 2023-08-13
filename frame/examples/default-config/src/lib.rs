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

//! # Default Config Pallet Example
//!
//! A simple example of a FRAME pallet that utilizes [`frame_support::derive_impl`] to demonstrate
//! the simpler way to implement `Config` trait of pallets. This example only showcases this in a
//! `mock.rs` environment, but the same applies to a real runtime as well.
//!
//! See the source code of [`tests`] for a real examples.
//!
//! Study the following types:
//!
//! - [`pallet::DefaultConfig`], and how it differs from [`pallet::Config`].
//! - [`pallet::config_preludes::TestDefaultConfig`] and how it implements
//!   [`pallet::DefaultConfig`].
//! - Notice how [`pallet::DefaultConfig`] is independent of [`frame_system::Config`].

#![cfg_attr(not(feature = "std"), no_std)]

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;

	/// This pallet is annotated to have a default config. This will auto-generate
	/// [`DefaultConfig`].
	///
	/// It will be an identical, but won't have anything that is `#[pallet::no_default]`.
	#[pallet::config(with_default)]
	pub trait Config: frame_system::Config {
		/// The overarching event type. This is coming from the runtime, and cannot have a default.
		/// In general, `Runtime*`-oriented types cannot have a sensible default.
		#[pallet::no_default] // optional. `RuntimeEvent` is automatically excluded as well.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// An input parameter to this pallet. This value can have a default, because it is not
		/// reliant on `frame_system::Config` or the overarching runtime in any way.
		type WithDefaultValue: Get<u32>;

		/// Same as [`Config::WithDefaultValue`], but we don't intend to define a default for this
		/// in our tests below.
		type OverwrittenDefaultValue: Get<u32>;

		/// An input parameter that relies on `<Self as frame_system::Config>::AccountId`. As of
		/// now, such types cannot have defaults and need to be annotated as such, iff
		/// `#[pallet::config(with_default)]` is enabled:
		#[pallet::no_default]
		type CannotHaveDefault: Get<Self::AccountId>;

		/// Something that is a normal type, with default.
		type WithDefaultType;

		/// Same as [`Config::WithDefaultType`], but we don't intend to define a default for this
		/// in our tests below.
		type OverwrittenDefaultType;
	}

	/// Container for different types that implement [`DefaultConfig`]` of this pallet.
	pub mod config_preludes {
		// This will help use not need to disambiguate anything when using `derive_impl`.
		use super::*;

		/// A type providing default configurations for this pallet in testing environment.
		pub struct TestDefaultConfig;
		#[frame_support::register_default_impl(TestDefaultConfig)]
		impl DefaultConfig for TestDefaultConfig {
			type WithDefaultValue = frame_support::traits::ConstU32<42>;
			type OverwrittenDefaultValue = frame_support::traits::ConstU32<42>;

			type WithDefaultType = u32;
			type OverwrittenDefaultType = u32;
		}

		/// A type providing default configurations for this pallet in a parachain environment.
		pub struct ParachainDefaultConfig;
		#[frame_support::register_default_impl(ParachainDefaultConfig)]
		impl DefaultConfig for ParachainDefaultConfig {
			type WithDefaultValue = frame_support::traits::ConstU32<66>;
			type OverwrittenDefaultValue = frame_support::traits::ConstU32<66>;
			type WithDefaultType = u32;
			type OverwrittenDefaultType = u32;
		}
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::event]
	pub enum Event<T: Config> {}
}

#[cfg(any(test, doc))]
pub mod tests {
	use super::*;
	use frame_support::derive_impl;
	use sp_runtime::traits::ConstU64;

	use super::pallet as pallet_default_config_example;

	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test
		{
			System: frame_system,
			DefaultPallet: pallet_default_config_example,
		}
	);

	#[derive_impl(frame_system::config_preludes::TestDefaultConfig as frame_system::DefaultConfig)]
	impl frame_system::Config for Test {
		// these items are defined by frame-system as `no_default`, so we must specify them here.
		// Note that these are types that actually rely on the outer runtime, and can't sensibly
		// have an _independent_ default.
		type Block = Block;
		type BlockHashCount = ConstU64<10>;
		type BaseCallFilter = frame_support::traits::Everything;
		type RuntimeOrigin = RuntimeOrigin;
		type RuntimeCall = RuntimeCall;
		type RuntimeEvent = RuntimeEvent;
		type PalletInfo = PalletInfo;
		type OnSetCode = ();

		// all of this is coming from `frame_system::config_preludes::TestDefaultConfig`.

		// type Nonce = u32;
		// type BlockNumber = u32;
		// type Header =
		// sp_runtime::generic::Header<frame_system::pallet_prelude::BlockNumberFor<Self>,
		// Self::Hashing>;
		// type Hash = sp_core::hash::H256;
		// type Hashing = sp_runtime::traits::BlakeTwo256;
		// type AccountId = u64;
		// type Lookup = sp_runtime::traits::IdentityLookup<u64>;
		// type BlockHashCount = frame_support::traits::ConstU32<10>;
		// type MaxConsumers = frame_support::traits::ConstU32<16>;
		// type AccountData = ();
		// type OnNewAccount = ();
		// type OnKilledAccount = ();
		// type SystemWeightInfo = ();
		// type SS58Prefix = ();
		// type Version = ();
		// type BlockWeights = ();
		// type BlockLength = ();
		// type DbWeight = ();

		// you could still overwrite any of them if desired.
		type SS58Prefix = frame_support::traits::ConstU16<456>;
	}

	// Similarly, we use the defaults provided by own crate as well.
	use pallet::config_preludes::*;
	#[derive_impl(TestDefaultConfig as pallet::DefaultConfig)]
	impl crate::pallet::Config for Test {
		// These two both cannot have defaults.
		type RuntimeEvent = RuntimeEvent;
		// Note that the default account-id type in
		// `frame_system::config_preludes::TestDefaultConfig` is `u64`.
		type CannotHaveDefault = frame_support::traits::ConstU64<1>;

		type OverwrittenDefaultValue = frame_support::traits::ConstU32<678>;
		type OverwrittenDefaultType = u128;
	}

	#[test]
	fn it_works() {
		use frame_support::traits::Get;
		use pallet::{Config, DefaultConfig};

		// assert one of the value types that is not overwritten.
		assert_eq!(
			<<Test as Config>::WithDefaultValue as Get<u32>>::get(),
			<<TestDefaultConfig as DefaultConfig>::WithDefaultValue as Get<u32>>::get()
		);

		// assert one of the value types that is overwritten.
		assert_eq!(<<Test as Config>::OverwrittenDefaultValue as Get<u32>>::get(), 678u32);

		// assert one of the types that is not overwritten.
		assert_eq!(
			std::any::TypeId::of::<<Test as Config>::WithDefaultType>(),
			std::any::TypeId::of::<<TestDefaultConfig as DefaultConfig>::WithDefaultType>()
		);

		// assert one of the types that is overwritten.
		assert_eq!(
			std::any::TypeId::of::<<Test as Config>::OverwrittenDefaultType>(),
			std::any::TypeId::of::<u128>()
		)
	}
}
