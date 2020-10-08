// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! # Timestamp Module
//!
//! The Timestamp module provides functionality to get and set the on-chain time.
//!
//! - [`timestamp::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! The Timestamp module allows the validators to set and validate a timestamp with each block.
//!
//! It uses inherents for timestamp data, which is provided by the block author and validated/verified
//! by other validators. The timestamp can be set only once per block and must be set each block.
//! There could be a constraint on how much time must pass before setting the new timestamp.
//!
//! **NOTE:** The Timestamp module is the recommended way to query the on-chain time instead of using
//! an approach based on block numbers. The block number based time measurement can cause issues
//! because of cumulative calculation errors and hence should be avoided.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! * `set` - Sets the current time.
//!
//! ### Public functions
//!
//! * `get` - Gets the current time for the current block. If this function is called prior to
//! setting the timestamp, it will return the timestamp of the previous block.
//!
//! ### Trait Getters
//!
//! * `MinimumPeriod` - Gets the minimum (and advised) period between blocks for the chain.
//!
//! ## Usage
//!
//! The following example shows how to use the Timestamp module in your custom module to query the current timestamp.
//!
//! ### Prerequisites
//!
//! Import the Timestamp module into your custom module and derive the module configuration
//! trait from the timestamp trait.
//!
//! ### Get current timestamp
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! # use pallet_timestamp as timestamp;
//! use frame_system::ensure_signed;
//!
//! pub trait Trait: timestamp::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		#[weight = 0]
//! 		pub fn get_time(origin) -> dispatch::DispatchResult {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _now = <timestamp::Module<T>>::get();
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() {}
//! ```
//!
//! ### Example from the FRAME
//!
//! The [Session module](https://github.com/paritytech/substrate/blob/master/frame/session/src/lib.rs) uses
//! the Timestamp module for session management.
//!
//! ## Related Modules
//!
//! * [Session](../pallet_session/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod default_weights;

use sp_std::{result, cmp};
use sp_inherents::{ProvideInherent, InherentData, InherentIdentifier};
#[cfg(feature = "std")]
use frame_support::debug;
use frame_support::{
	Parameter, decl_storage, decl_module,
	traits::{Time, UnixTime, Get},
	weights::{DispatchClass, Weight},
};
use sp_runtime::{
	RuntimeString,
	traits::{
		AtLeast32Bit, Zero, SaturatedConversion, Scale,
	}
};
use frame_system::ensure_none;
use sp_timestamp::{
	InherentError, INHERENT_IDENTIFIER, InherentType,
	OnTimestampSet,
};

pub trait WeightInfo {
	fn set() -> Weight;
	fn on_finalize() -> Weight;
}

/// The module configuration trait
pub trait Trait: frame_system::Trait {
	/// Type used for expressing timestamp.
	type Moment: Parameter + Default + AtLeast32Bit
		+ Scale<Self::BlockNumber, Output = Self::Moment> + Copy;

	/// Something which can be notified when the timestamp is set. Set this to `()` if not needed.
	type OnTimestampSet: OnTimestampSet<Self::Moment>;

	/// The minimum period between blocks. Beware that this is different to the *expected* period
	/// that the block production apparatus provides. Your chosen consensus system will generally
	/// work with this to determine a sensible block time. e.g. For Aura, it will be double this
	/// period on default settings.
	type MinimumPeriod: Get<Self::Moment>;

	/// Weight information for extrinsics in this pallet.
	type WeightInfo: WeightInfo;
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// The minimum period between blocks. Beware that this is different to the *expected* period
		/// that the block production apparatus provides. Your chosen consensus system will generally
		/// work with this to determine a sensible block time. e.g. For Aura, it will be double this
		/// period on default settings.
		const MinimumPeriod: T::Moment = T::MinimumPeriod::get();

		/// Set the current time.
		///
		/// This call should be invoked exactly once per block. It will panic at the finalization
		/// phase, if this call hasn't been invoked by that time.
		///
		/// The timestamp should be greater than the previous one by the amount specified by
		/// `MinimumPeriod`.
		///
		/// The dispatch origin for this call must be `Inherent`.
		///
		/// # <weight>
		/// - `O(1)` (Note that implementations of `OnTimestampSet` must also be `O(1)`)
		/// - 1 storage read and 1 storage mutation (codec `O(1)`). (because of `DidUpdate::take` in `on_finalize`)
		/// - 1 event handler `on_timestamp_set`. Must be `O(1)`.
		/// # </weight>
		#[weight = (
			T::WeightInfo::set(),
			DispatchClass::Mandatory
		)]
		fn set(origin, #[compact] now: T::Moment) {
			ensure_none(origin)?;
			assert!(!<Self as Store>::DidUpdate::exists(), "Timestamp must be updated only once in the block");
			let prev = Self::now();
			assert!(
				prev.is_zero() || now >= prev + T::MinimumPeriod::get(),
				"Timestamp must increment by at least <MinimumPeriod> between sequential blocks"
			);
			<Self as Store>::Now::put(now);
			<Self as Store>::DidUpdate::put(true);

			<T::OnTimestampSet as OnTimestampSet<_>>::on_timestamp_set(now);
		}

		/// dummy `on_initialize` to return the weight used in `on_finalize`.
		fn on_initialize() -> Weight {
			// weight of `on_finalize`
			T::WeightInfo::on_finalize()
		}

		/// # <weight>
		/// - `O(1)`
		/// - 1 storage deletion (codec `O(1)`).
		/// # </weight>
		fn on_finalize() {
			assert!(<Self as Store>::DidUpdate::take(), "Timestamp must be updated once in the block");
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Timestamp {
		/// Current time for the current block.
		pub Now get(fn now) build(|_| 0.into()): T::Moment;

		/// Did the timestamp get updated in this block?
		DidUpdate: bool;
	}
}

impl<T: Trait> Module<T> {
	/// Get the current time for the current block.
	///
	/// NOTE: if this function is called prior to setting the timestamp,
	/// it will return the timestamp of the previous block.
	pub fn get() -> T::Moment {
		Self::now()
	}

	/// Set the timestamp to something in particular. Only used for tests.
	#[cfg(feature = "std")]
	pub fn set_timestamp(now: T::Moment) {
		<Self as Store>::Now::put(now);
	}
}

fn extract_inherent_data(data: &InherentData) -> Result<InherentType, RuntimeString> {
	data.get_data::<InherentType>(&INHERENT_IDENTIFIER)
		.map_err(|_| RuntimeString::from("Invalid timestamp inherent data encoding."))?
		.ok_or_else(|| "Timestamp inherent data is not provided.".into())
}

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = Call<T>;
	type Error = InherentError;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(data: &InherentData) -> Option<Self::Call> {
		let data: T::Moment = extract_inherent_data(data)
			.expect("Gets and decodes timestamp inherent data")
			.saturated_into();

		let next_time = cmp::max(data, Self::now() + T::MinimumPeriod::get());
		Some(Call::set(next_time.into()))
	}

	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		const MAX_TIMESTAMP_DRIFT_MILLIS: u64 = 30 * 1000;

		let t: u64 = match call {
			Call::set(ref t) => t.clone().saturated_into::<u64>(),
			_ => return Ok(()),
		};

		let data = extract_inherent_data(data).map_err(|e| InherentError::Other(e))?;

		let minimum = (Self::now() + T::MinimumPeriod::get()).saturated_into::<u64>();
		if t > data + MAX_TIMESTAMP_DRIFT_MILLIS {
			Err(InherentError::Other("Timestamp too far in future to accept".into()))
		} else if t < minimum {
			Err(InherentError::ValidAtTimestamp(minimum))
		} else {
			Ok(())
		}
	}
}

impl<T: Trait> Time for Module<T> {
	type Moment = T::Moment;

	/// Before the first set of now with inherent the value returned is zero.
	fn now() -> Self::Moment {
		Self::now()
	}
}

/// Before the timestamp inherent is applied, it returns the time of previous block.
///
/// On genesis the time returned is not valid.
impl<T: Trait> UnixTime for Module<T> {
	fn now() -> core::time::Duration {
		// now is duration since unix epoch in millisecond as documented in
		// `sp_timestamp::InherentDataProvider`.
		let now = Self::now();
		sp_std::if_std! {
			if now == T::Moment::zero() {
				debug::error!(
					"`pallet_timestamp::UnixTime::now` is called at genesis, invalid value returned: 0"
				);
			}
		}
		core::time::Duration::from_millis(now.saturated_into::<u64>())
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use frame_support::{impl_outer_origin, assert_ok, parameter_types, weights::Weight};
	use sp_io::TestExternalities;
	use sp_core::H256;
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};

	pub fn new_test_ext() -> TestExternalities {
		let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		TestExternalities::new(t)
	}

	impl_outer_origin! {
		pub enum Origin for Test where system = frame_system {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type BaseCallFilter = ();
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumExtrinsicWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
		type PalletInfo = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
	}
	parameter_types! {
		pub const MinimumPeriod: u64 = 5;
	}
	impl Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
		type MinimumPeriod = MinimumPeriod;
		type WeightInfo = ();
	}
	type Timestamp = Module<Test>;

	#[test]
	fn timestamp_works() {
		new_test_ext().execute_with(|| {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::set(Origin::none(), 69));
			assert_eq!(Timestamp::now(), 69);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must be updated only once in the block")]
	fn double_timestamp_should_fail() {
		new_test_ext().execute_with(|| {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::set(Origin::none(), 69));
			let _ = Timestamp::set(Origin::none(), 70);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must increment by at least <MinimumPeriod> between sequential blocks")]
	fn block_period_minimum_enforced() {
		new_test_ext().execute_with(|| {
			Timestamp::set_timestamp(42);
			let _ = Timestamp::set(Origin::none(), 46);
		});
	}
}
