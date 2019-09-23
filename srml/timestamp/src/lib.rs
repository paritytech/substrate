// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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
//! use support::{decl_module, dispatch::Result};
//! # use srml_timestamp as timestamp;
//! use system::ensure_signed;
//!
//! pub trait Trait: timestamp::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn get_time(origin) -> Result {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _now = <timestamp::Module<T>>::get();
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() {}
//! ```
//!
//! ### Example from the SRML
//!
//! The [Session module](https://github.com/paritytech/substrate/blob/master/srml/session/src/lib.rs) uses
//! the Timestamp module for session management.
//!
//! ## Related Modules
//!
//! * [Session](../srml_session/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::{result, cmp};
use codec::Encode;
#[cfg(feature = "std")]
use codec::Decode;
#[cfg(feature = "std")]
use inherents::ProvideInherentData;
use support::{Parameter, decl_storage, decl_module};
use support::traits::{Time, Get};
use sr_primitives::traits::{
	SimpleArithmetic, Zero, SaturatedConversion, Scale
};
use sr_primitives::weights::SimpleDispatchInfo;
use system::ensure_none;
use inherents::{RuntimeString, InherentIdentifier, ProvideInherent, IsFatalError, InherentData};

/// The identifier for the `timestamp` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"timstap0";
/// The type of the inherent.
pub type InherentType = u64;

/// Errors that can occur while checking the timestamp inherent.
#[derive(Encode)]
#[cfg_attr(feature = "std", derive(Debug, Decode))]
pub enum InherentError {
	/// The timestamp is valid in the future.
	/// This is a non-fatal-error and will not stop checking the inherents.
	ValidAtTimestamp(InherentType),
	/// Some other error.
	Other(RuntimeString),
}

impl IsFatalError for InherentError {
	fn is_fatal_error(&self) -> bool {
		match self {
			InherentError::ValidAtTimestamp(_) => false,
			InherentError::Other(_) => true,
		}
	}
}

impl InherentError {
	/// Try to create an instance ouf of the given identifier and data.
	#[cfg(feature = "std")]
	pub fn try_from(id: &InherentIdentifier, data: &[u8]) -> Option<Self> {
		if id == &INHERENT_IDENTIFIER {
			<InherentError as codec::Decode>::decode(&mut &data[..]).ok()
		} else {
			None
		}
	}
}

/// Auxiliary trait to extract timestamp inherent data.
pub trait TimestampInherentData {
	/// Get timestamp inherent data.
	fn timestamp_inherent_data(&self) -> Result<InherentType, RuntimeString>;
}

impl TimestampInherentData for InherentData {
	fn timestamp_inherent_data(&self) -> Result<InherentType, RuntimeString> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Timestamp inherent data not found".into()))
	}
}

#[cfg(feature = "std")]
pub struct InherentDataProvider;

#[cfg(feature = "std")]
impl ProvideInherentData for InherentDataProvider {
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), RuntimeString> {
		use std::time::SystemTime;

		let now = SystemTime::now();
		now.duration_since(SystemTime::UNIX_EPOCH)
			.map_err(|_| {
				"Current time is before unix epoch".into()
			}).and_then(|d| {
				let duration: InherentType = d.as_millis() as u64;
				inherent_data.put_data(INHERENT_IDENTIFIER, &duration)
			})
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		InherentError::try_from(&INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}

/// A trait which is called when the timestamp is set.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait OnTimestampSet<Moment> {
	fn on_timestamp_set(moment: Moment);
}

/// The module configuration trait
pub trait Trait: system::Trait {
	/// Type used for expressing timestamp.
	type Moment: Parameter + Default + SimpleArithmetic
		+ Scale<Self::BlockNumber, Output = Self::Moment> + Copy;

	/// Something which can be notified when the timestamp is set. Set this to `()` if not needed.
	type OnTimestampSet: OnTimestampSet<Self::Moment>;

	/// The minimum period between blocks. Beware that this is different to the *expected* period
	/// that the block production apparatus provides. Your chosen consensus system will generally
	/// work with this to determine a sensible block time. e.g. For Aura, it will be double this
	/// period on default settings.
	type MinimumPeriod: Get<Self::Moment>;
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
		#[weight = SimpleDispatchInfo::FixedOperational(10_000)]
		fn set(origin, #[compact] now: T::Moment) {
			ensure_none(origin)?;
			assert!(!<Self as Store>::DidUpdate::exists(), "Timestamp must be updated only once in the block");
			assert!(
				Self::now().is_zero() || now >= Self::now() + T::MinimumPeriod::get(),
				"Timestamp must increment by at least <MinimumPeriod> between sequential blocks"
			);
			<Self as Store>::Now::put(now);
			<Self as Store>::DidUpdate::put(true);

			<T::OnTimestampSet as OnTimestampSet<_>>::on_timestamp_set(now);
		}

		fn on_finalize() {
			assert!(<Self as Store>::DidUpdate::take(), "Timestamp must be updated once in the block");
		}
	}
}

decl_storage! {
	trait Store for Module<T: Trait> as Timestamp {
		/// Current time for the current block.
		pub Now get(now) build(|_| 0.into()): T::Moment;

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
		const MAX_TIMESTAMP_DRIFT: u64 = 60;

		let t: u64 = match call {
			Call::set(ref t) => t.clone().saturated_into::<u64>(),
			_ => return Ok(()),
		};

		let data = extract_inherent_data(data).map_err(|e| InherentError::Other(e))?;

		let minimum = (Self::now() + T::MinimumPeriod::get()).saturated_into::<u64>();
		if t > data + MAX_TIMESTAMP_DRIFT {
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

#[cfg(test)]
mod tests {
	use super::*;

	use support::{impl_outer_origin, assert_ok, parameter_types};
	use runtime_io::{with_externalities, TestExternalities};
	use primitives::H256;
	use sr_primitives::{Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header};

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Call = ();
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type AvailableBlockRatio = AvailableBlockRatio;
		type MaximumBlockLength = MaximumBlockLength;
		type Version = ();
	}
	parameter_types! {
		pub const MinimumPeriod: u64 = 5;
	}
	impl Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
		type MinimumPeriod = MinimumPeriod;
	}
	type Timestamp = Module<Test>;

	#[test]
	fn timestamp_works() {
		let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::dispatch(Call::set(69), Origin::NONE));
			assert_eq!(Timestamp::now(), 69);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must be updated only once in the block")]
	fn double_timestamp_should_fail() {
		let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			assert_ok!(Timestamp::dispatch(Call::set(69), Origin::NONE));
			let _ = Timestamp::dispatch(Call::set(70), Origin::NONE);
		});
	}

	#[test]
	#[should_panic(expected = "Timestamp must increment by at least <MinimumPeriod> between sequential blocks")]
	fn block_period_minimum_enforced() {
		let t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		with_externalities(&mut TestExternalities::new(t), || {
			Timestamp::set_timestamp(42);
			let _ = Timestamp::dispatch(Call::set(46), Origin::NONE);
		});
	}
}
