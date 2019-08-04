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

//! # Rolling Window module
//!
//! ## Overview
//!
//! The Rolling Window Module is similar to `simple moving average` except
//! that it just reports the number of occurrences in the window instead of
//! calculating the average.
//!
//! It is mainly implemented to keep track of misbehaviors and only to take
//! the last `sessions` of misbehaviors into account.
//!

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs, rust_2018_idioms)]

#[cfg(test)]
mod mock;

use srml_support::{
	StorageMap, Parameter, EnumerableStorageMap, decl_module, decl_storage,
	traits::SlashingOffence,
};
use parity_codec::{Codec, Decode, Encode};
use rstd::vec::Vec;
use sr_primitives::traits::{Member, MaybeSerializeDebug, TypedKey};
use srml_session::{SessionIndex, OneSessionHandler};

/// Rolling Window trait
pub trait Trait: system::Trait {
	/// Identifier type to implement `OneSessionHandler`
	type SessionKey: Member + Parameter + Default + TypedKey + Decode + Encode + AsRef<[u8]>;
}

type Id = [u8; 16];
type WindowLength = u32;

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Misbehavior reports
		///
		/// It stores every unique misbehavior of a kind
		// TODO [#3149]: optimize how to shrink the window when sessions expire
		MisbehaviorReports get(misbehavior_reports): linked_map Id => Vec<(SessionIndex, WindowLength)>;

		/// Bonding Uniqueness
		///
		/// Keeps track of uniquely reported misconducts in the entire bonding duration
		/// which is currently unbounded (insert only)
		///
		/// Footprints need to be unique or stash accounts must be banned from joining
		/// the validator set after been slashed
		BondingUniqueness get(bonding_uniqueness): linked_map T::Hash => SessionIndex;
	}
}

decl_module! {
	/// Rolling Window module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

/// Trait for getting the number of misbehaviors in the current window
pub trait GetMisbehaviors {
	/// Get number of misbehavior's in the current window for a kind
	fn get_misbehaviors(id: Id) -> u64;
}

impl<T: Trait> GetMisbehaviors for Module<T> {
	fn get_misbehaviors(id: Id) -> u64 {
		MisbehaviorReports::get(id).len() as u64
	}
}

/// Trait for reporting misbehavior's
pub trait MisbehaviorReporter<Hash> {
	/// Report misbehavior for a kind
	fn report_misbehavior(
		id: Id,
		window_length: WindowLength,
		footprint: Hash,
		current_session: SessionIndex
	) -> Result<(), ()>;
}

impl<T: Trait> MisbehaviorReporter<T::Hash> for Module<T> {
	fn report_misbehavior(
		id: Id,
		window_length: WindowLength,
		footprint: T::Hash,
		current_session: SessionIndex,
	) -> Result<(), ()> {
		if <BondingUniqueness<T>>::exists(footprint) {
			Err(())
		} else {
			<BondingUniqueness<T>>::insert(footprint, current_session);
			MisbehaviorReports::mutate(id, |entry| entry.push((current_session, window_length)));
			Ok(())
		}
	}
}

impl<T: Trait> OneSessionHandler<T::SessionKey> for Module<T>
{
	type Key = T::SessionKey;

	fn on_new_session<'a, I: 'a>(
		(ended_session, _new_session): (SessionIndex, SessionIndex),
		_changed: bool,
		_validators: I,
		_queued_validators: I,
	) {
		for (kind, _) in MisbehaviorReports::enumerate() {
			MisbehaviorReports::mutate(kind, |reports| {
				// it is guaranteed that `reported_session` happened in the same session or before `ending`
				reports.retain(|(reported_session, window_length)| {
					let diff = ended_session.wrapping_sub(*reported_session);
					diff < *window_length
				});
			});
		}
	}

	// ignored
	fn on_disabled(_: usize) {}
}

/// Macro for implement static `base_severity` which may be used for misconducts implementations
#[macro_export]
macro_rules! impl_base_severity {
	// type with type parameters
	($ty:ident < $( $N:ident $(: $b0:ident $(+$b:ident)* )? ),* >, $t: ty : $seve: expr) => {
		impl< $( $N $(: $b0 $(+$b)* )? ),* > $ty< $( $N ),* > {
			fn base_severity() -> $t {
				$seve
			}
		}
	};
	// type without type parameters
	($ty:ident, $t: ty : $seve: expr) => {
		impl $ty {
			fn base_severity() -> $t {
				$seve
			}
		}
	};
}

/// Macro for implement static `misconduct kind` which may be used for misconducts implementations
/// Note, that the kind need to implement the `WindowLength` trait to work
#[macro_export]
macro_rules! impl_kind {
	// type with type parameters
	($ty:ident < $( $N:ident $(: $b0:ident $(+$b:ident)* )? ),* >, $t: ty : $kind: expr) => {

		impl< $( $N $(: $b0 $(+$b)* )? ),* > $ty< $( $N ),* > {
			fn kind() -> $t {
				$kind
			}
		}
	};
	// type without type parameters
	($ty:ident, $t: ty : $kind: expr) => {
		impl $ty {
			fn kind() -> $t {
				$kind
			}
		}
	};
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::iter::empty;
	use runtime_io::with_externalities;
	use crate::mock::*;
	use substrate_primitives::H256;
	use srml_support::{assert_ok, assert_noop};

	type RollingWindow = Module<Test>;

	#[test]
	fn it_works() {
		with_externalities(&mut new_test_ext(), || {
			let zero = H256::zero();
			let one: H256 = [1_u8; 32].into();
			let two: H256 = [2_u8; 32].into();

			let mut current_session = 0;

			assert_ok!(RollingWindow::report_misbehavior(Kind::Two, zero, current_session));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 1);
			assert_noop!(RollingWindow::report_misbehavior(Kind::Two, zero, current_session), ());

			assert_ok!(RollingWindow::report_misbehavior(Kind::Two, one, current_session));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 2);
			assert_noop!(RollingWindow::report_misbehavior(Kind::Two, one, current_session), ());

			current_session += 1;
			RollingWindow::on_new_session((current_session - 1, current_session), false, empty(), empty());

			assert_ok!(RollingWindow::report_misbehavior(Kind::Two, two, current_session));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 3);

			current_session += 1;

			RollingWindow::on_new_session((current_session - 1, current_session), false, empty(), empty());
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 3);

			current_session += 1;
			RollingWindow::on_new_session((current_session - 1, current_session), false, empty(), empty());
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 3);

			current_session += 1;
			RollingWindow::on_new_session((current_session - 1, current_session), false, empty(), empty());
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 1);
		});
	}

	#[test]
	fn bonding_unbounded() {
		with_externalities(&mut new_test_ext(), || {
			let zero = H256::zero();
			let one: H256 = [1_u8; 32].into();

			assert_ok!(RollingWindow::report_misbehavior(Kind::Two, zero, 0));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 1);
			assert_noop!(RollingWindow::report_misbehavior(Kind::One, zero, 0), ());
			assert_ok!(RollingWindow::report_misbehavior(Kind::Two, one, 0));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Two), 2);

			// rolling window has expired but bonding_uniqueness shall be unbounded
			RollingWindow::on_new_session((50, 51), false, empty(), empty());

			assert_noop!(RollingWindow::report_misbehavior(Kind::Two, zero, 51), ());
			assert_noop!(RollingWindow::report_misbehavior(Kind::One, one, 52), ());
		});
	}

	#[test]
	fn rolling_window_wrapped() {
		with_externalities(&mut new_test_ext(), || {
			// window length is u32::max_value should expire at session 24
			assert_ok!(RollingWindow::report_misbehavior(Kind::Four, H256::zero(), 25));
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Four), 1);

			// `u32::max_value() - 25` sessions have been executed
			RollingWindow::on_new_session((u32::max_value(), 0), false, empty(), empty());
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Four), 1);

			for session in 0..24 {
				RollingWindow::on_new_session((session, session + 1), false, empty(), empty());
				assert_eq!(RollingWindow::get_misbehaviors(Kind::Four), 1);
			}

			// `u32::max_value` sessions have been executed should removed from the window
			RollingWindow::on_new_session((24, 25), false, empty(), empty());
			assert_eq!(RollingWindow::get_misbehaviors(Kind::Four), 0);
		});
	}

	#[test]
	fn macros() {
		use rstd::marker::PhantomData;

		struct Bar;

		struct Foo<T, U>(PhantomData<(T, U)>);

		impl_base_severity!(Bar, usize: 1);
		impl_base_severity!(Foo<T, U>, usize: 1337);
		impl_kind!(Bar, Kind: Kind::One);
		impl_kind!(Foo<T, U>, Kind: Kind::Two);

		assert_eq!(Bar::base_severity(), 1);
		assert_eq!(Foo::<u32, u64>::base_severity(), 1337);
		assert_eq!(Bar::kind(), Kind::One);
		assert_eq!(Foo::<u32, u64>::kind(), Kind::Two);
	}
}
