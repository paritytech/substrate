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
//! It is mainly implemented to keep track of misbehaviors and only the take
//! the last `sessions` of misbehaviors into account.
//!

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs, rust_2018_idioms)]

#[cfg(test)]
mod mock;

use srml_support::{
	StorageMap, EnumerableStorageMap, decl_module, decl_storage,
	traits::{Get, WindowLength}
};
use parity_codec::Codec;
use sr_primitives::traits::MaybeSerializeDebug;
use srml_session::SessionIndex;
use srml_staking::EraIndex;

/// Rolling Window trait
pub trait Trait: system::Trait {
	/// Kind to report with window length
	type Kind: Copy + Clone + Codec + MaybeSerializeDebug + WindowLength<u32>;

	/// Number of eras that staked funds must remain bonded for.
	type BondingDuration: Get<EraIndex>;
}

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Misbehavior reports
		///
		/// It stores every unique misbehavior of a kind
		// TODO(niklasad1): optimize how to shrink the window when sessions expire
		MisconductReports get(kind): linked_map T::Kind => Vec<SessionIndex>;

		/// EraData which have mapping from `EraIndex` to a unique Hash
		///
		EraData get(idx): linked_map EraIndex => Vec<T::Hash>;

		/// Bonding guard
		///
		/// Keeps track of uniquely reported misconducts in the entire bonding duration
		/// It will be unbounded
		BondingUniqueness get(uniq): linked_map T::Hash => SessionIndex;
	}
}

decl_module! {
	/// Rolling Window module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {
	/// Report misbehavior for a kind
	///
	/// If the misbehavior is not unique `Err` is returned otherwise the number of misbehaviors for the kind
	/// is returned
	pub fn report_misbehavior(
		kind: T::Kind,
		footprint: T::Hash,
		current_session: SessionIndex,
		current_era: EraIndex
	) -> Result<u64, ()> {

		// filter out misconduct uniqueness over 1 period old
		Self::refresh(current_era);

		if <BondingUniqueness<T>>::exists(footprint) {
			return Err(());
		} else {
			<BondingUniqueness<T>>::insert(footprint, current_session);
		}

		<EraData<T>>::mutate(current_era, |entry| entry.push(footprint));
		<MisconductReports<T>>::mutate(kind, |entry| entry.push(current_session));

		Ok(<MisconductReports<T>>::get(kind).len() as u64)
	}

	// TODO(niklasad1): get bonding duration from Staking
	fn refresh(current_era: EraIndex) {
		let bonding_duration = T::BondingDuration::get();

		for (idx, _) in <EraData<T>>::enumerate() {
			let diff = current_era.wrapping_sub(idx);
			if diff >= bonding_duration {
				for old in <EraData<T>>::take(idx) {
					<BondingUniqueness<T>>::remove(old);
				}
			}
		}
	}

	/// Return number of misbehavior's in the current window
	pub fn get_misbehaved(kind: T::Kind) -> u64 {
		<MisconductReports<T>>::get(kind).len() as u64
	}
}

impl<T: Trait> srml_session::OnSessionEnding<T::AccountId> for Module<T> {
	fn on_session_ending(ending: SessionIndex, _applied_at: SessionIndex) -> Option<Vec<T::AccountId>> {
		for (kind, _) in <MisconductReports<T>>::enumerate() {
			let window_length = kind.window_length();
			<MisconductReports<T>>::mutate(kind, |reports| {
				// it is guaranteed that `reported_session` happened before `end`
				reports.retain(|reported_session| {
					let diff = ending.wrapping_sub(*reported_session);
					diff < *window_length
				});
			});
		}

		// don't provide a new validator set
		None
	}
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
	use runtime_io::with_externalities;
	use crate::mock::*;
	use substrate_primitives::H256;
	use srml_session::OnSessionEnding;

	type RollingWindow = Module<Test>;

	#[test]
	fn it_works() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {

			let zero = H256::zero();
			let one: H256 = [1_u8; 32].into();
			let two: H256 = [2_u8; 32].into();

			let mut current_session = 0;
			let current_era = 0;

			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, zero, current_session, current_era).unwrap(), 1);
			assert!(RollingWindow::report_misbehavior(Kind::Two, zero, current_session, current_era).is_err());

			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, one, current_session, current_era).unwrap(), 2);
			assert!(RollingWindow::report_misbehavior(Kind::Two, one, current_session, current_era).is_err());


			RollingWindow::on_session_ending(current_session, current_session + 1);

			current_session += 1;

			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, two, current_session, current_era).unwrap(), 3);
			RollingWindow::on_session_ending(current_session, current_session + 1);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 3);

			current_session += 1;

			RollingWindow::on_session_ending(current_session, current_session + 1);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 3);

			current_session += 1;

			RollingWindow::on_session_ending(current_session, current_session + 1);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 1);
		});
	}

	#[test]
	fn bonding_uniqueness_simple() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {

			let zero = H256::zero();
			let one: H256 = [1_u8; 32].into();

			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, zero, 0, 0).unwrap(), 1);
			assert!(RollingWindow::report_misbehavior(Kind::One, zero, 0, 0).is_err());
			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, one, 0, 1).unwrap(), 2);

			for era in 1..3 {
				assert!(RollingWindow::report_misbehavior(Kind::Two, zero, 0, era).is_err());
			}

			// bonding period expired but not the rolling window
			assert_eq!(RollingWindow::report_misbehavior(Kind::Two, zero, 0, 3).unwrap(), 3);

		});
	}

	#[test]
	fn rolling_window_wrapped() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {

			let era_index = 0;

			// window length is u32::max_value should expire at session 24
			assert_eq!(RollingWindow::report_misbehavior(Kind::Four, H256::zero(), 25, era_index).unwrap(), 1);

			// `u32::max_value() - 25` sessions have been executed
			RollingWindow::on_session_ending(u32::max_value(), 0);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Four), 1);

			for session in 0..24 {
				RollingWindow::on_session_ending(session, session + 1);
				assert_eq!(RollingWindow::get_misbehaved(Kind::Four), 1);
			}

			// `u32::max_value` sessions have been executed should removed from the window
			RollingWindow::on_session_ending(24, 25);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Four), 0);
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
