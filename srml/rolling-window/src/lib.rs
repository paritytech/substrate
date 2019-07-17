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
	StorageValue, StorageMap, EnumerableStorageMap, decl_module, decl_storage,
	traits::WindowLength
};
use parity_codec::Codec;
use sr_primitives::traits::MaybeSerializeDebug;

type Session = u32;

/// Rolling Window trait
pub trait Trait: system::Trait {
	/// Kind to report with window length
	type Kind: Copy + Clone + Codec + MaybeSerializeDebug + WindowLength<u32>;
}

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Misbehavior reports
		///
		/// It maps each kind into a hash (identity of reporter) and session number when it occurred
		MisconductReports get(kind): linked_map T::Kind => Vec<(Session, T::Hash)>;

		/// Session index
		SessionIndex get(s) config(): u32 = 0;
	}
}

decl_module! {
	/// Rolling Window module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {
	/// Remove items that doesn't fit into the rolling window
	/// Must be called when a session ends
	pub fn on_session_end() {
		let session = SessionIndex::get().wrapping_add(1);

		for (kind, _) in <MisconductReports<T>>::enumerate() {
			let window_length = kind.window_length();
			<MisconductReports<T>>::mutate(kind, |reports| {
				// it is guaranteed that `reported_session` happened before `session`
				reports.retain(|(reported_session, _)| {
					let diff = session.wrapping_sub(*reported_session);
					diff < *window_length
				});
			});
		}

		SessionIndex::put(session);
	}

	/// Report misbehavior for a kind
	pub fn report_misbehavior(kind: T::Kind, footprint: T::Hash) {
		let session = SessionIndex::get();

		if <MisconductReports<T>>::exists(kind) {
			<MisconductReports<T>>::mutate(kind, |w| w.push((session, footprint)));
		} else {
			<MisconductReports<T>>::insert(kind, vec![(session, footprint)]);
		}
	}

	/// Return number of misbehavior's in the current window which
	/// may include duplicated misbehaviour's
	pub fn get_misbehaved(kind: T::Kind) -> u64 {
		<MisconductReports<T>>::get(kind).len() as u64
	}


	/// Return number of misbehavior's in the current window which
	/// ignores duplicated misbehavior's in each session
	pub fn get_misbehaved_unique(kind: T::Kind) -> u64 {
		let window = <MisconductReports<T>>::get(kind);

		let mut seen_ids = rstd::vec::Vec::new();
		let mut unique = 0_u64;
		let mut last_seen_session = 0;

		for (session, id) in window {
			// new session reset `seen_ids`
			if session > last_seen_session {
				seen_ids.clear();
			}

			// Unfortunately O(n)
			if !seen_ids.contains(&id) {
				unique = unique.saturating_add(1);
				seen_ids.push(id);
			}

			last_seen_session = session;
		}

		unique
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

	type RollingWindow = Module<Test>;


	#[test]
	fn it_works() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {

			for i in 1..=10 {
				RollingWindow::report_misbehavior(Kind::One, H256::zero());
				assert_eq!(RollingWindow::get_misbehaved(Kind::One), i);
			}

			for i in 1..=4 {
				RollingWindow::report_misbehavior(Kind::Two, H256::zero());
				assert_eq!(RollingWindow::get_misbehaved(Kind::Two), i);
			}

			RollingWindow::on_session_end();
			// session = 1
			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 10);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 4);

			RollingWindow::on_session_end();
			// session = 2
			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 10);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 4);

			RollingWindow::on_session_end();
			// session = 3
			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 10);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 0);

			RollingWindow::on_session_end();
			// session = 4
			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 0);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 0);

		});
	}

	#[test]
	fn unique() {
		with_externalities(&mut ExtBuilder::default()
			.build(),
		|| {
			let one: H256 = [1_u8; 32].into();
			let two: H256 = [2_u8; 32].into();

			for _ in 0..10 {
				RollingWindow::report_misbehavior(Kind::Two, H256::zero());
			}

			for _ in 0..33 {
				RollingWindow::report_misbehavior(Kind::Three, H256::zero());
			}

			RollingWindow::report_misbehavior(Kind::Two, one);
			RollingWindow::report_misbehavior(Kind::Two, two);

			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 12);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 3);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Three), 33);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Three), 1);
			RollingWindow::on_session_end();
			// session index = 1

			for _ in 0..5 {
				RollingWindow::report_misbehavior(Kind::Two, H256::zero());
			}

			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 17);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 4);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Three), 33);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Three), 1);
			RollingWindow::on_session_end();
			// session index = 2
			// Kind::Three should have been expired

			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 17);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 4);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Three), 0);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Three), 0);
			RollingWindow::on_session_end();
			// session index = 3
			// events that happend in session 0 should have been expired

			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 5);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 1);
		});
	}


	#[test]
	fn macros() {
		use rstd::marker::PhantomData;

		struct Bar;

		struct Foo<T, U>((PhantomData<T>, PhantomData<U>));

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
