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
};
use parity_codec::Codec;
use sr_primitives::traits::MaybeSerializeDebug;

type WindowLength = u32;
type Session = u32;

/// Rolling Window trait
pub trait Trait: system::Trait {
	/// Kind to report
	type Kind: Copy + Clone + Codec + MaybeSerializeDebug;
}

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Misbehavior reports
		///
		/// It maps each kind into a hash (identity of reporter), window_length and session number when it occurred
		MisconductReports get(kind): linked_map T::Kind => Vec<(Session, WindowLength, T::Hash)>;

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
	pub fn on_session_end() {
		let session = match SessionIndex::get().wrapping_add(1);

		for (kind, _) in <MisconductReports<T>>::enumerate() {
			<MisconductReports<T>>::mutate(kind, |window| {
				// it is guaranteed that `reported_session` happened before `session`
				window.retain(|(reported_session, window_length, _)| {

					let diff = session.wrapping_sub(reported_session);
					diff < window_length
				});
			});
		}

		SessionIndex::put(session);
	}

	/// Report misbehaviour for a kind
	///
	/// If a non-existing kind is reported it is ignored
	pub fn report_misbehavior(kind: T::Kind, window_length: u32, footprint: T::Hash) {
		let session = SessionIndex::get();

		if <MisconductReports<T>>::exists(kind) {
			<MisconductReports<T>>::mutate(kind, |w| w.push((session, window_length, footprint)));
		} else {
			<MisconductReports<T>>::insert(kind, vec![(session, window_length, footprint)]);
		}
	}

	/// Return number of misbehaviors in the current window which
	/// may include duplicated misbehaviours
	pub fn get_misbehaved(kind: T::Kind) -> u64 {
		<MisconductReports<T>>::get(kind).len() as u64
	}


	/// Return number of misbehaviors in the current window which
	/// ignores duplicated misbehaviours in each session
	pub fn get_misbehaved_unique(kind: T::Kind) -> u64 {
		let window = <MisconductReports<T>>::get(kind);

		let mut seen_ids = rstd::vec::Vec::new();
		let mut unique = 0;
		// session can never be smaller than 0
		let mut last_session = 0;

		for (session, _, id) in window {
			// new session reset `seen_ids`
			if session > last_session {
				seen_ids.clear();
			}

			// Unfortunately O(n)
			if !seen_ids.contains(&id) {
				unique += 1;
				seen_ids.push(id);
			}

			last_session = session;
		}

		unique
	}
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

			const WINDOW_ONE: u32 = 4;
			const WINDOW_TWO: u32 = 3;


			for i in 1..=10 {
				RollingWindow::report_misbehavior(Kind::One, WINDOW_ONE, H256::zero());
				assert_eq!(RollingWindow::get_misbehaved(Kind::One), i);
			}

			for i in 1..=4 {
				RollingWindow::report_misbehavior(Kind::Two, WINDOW_TWO, H256::zero());
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
			const WINDOW_ONE: u32 = 3;
			const WINDOW_TWO: u32 = 2;

			let one: H256 = [1_u8; 32].into();
			let two: H256 = [2_u8; 32].into();

			for _ in 0..10 {
				RollingWindow::report_misbehavior(Kind::One, WINDOW_ONE, H256::zero());
			}

			for _ in 0..33 {
				RollingWindow::report_misbehavior(Kind::Two, WINDOW_TWO, H256::zero());
			}

			RollingWindow::report_misbehavior(Kind::One, WINDOW_ONE, one);
			RollingWindow::report_misbehavior(Kind::One, WINDOW_ONE, two);

			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 12);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::One), 3);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 33);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 1);
			RollingWindow::on_session_end();
			// session index = 1

			for _ in 0..5 {
				RollingWindow::report_misbehavior(Kind::One, WINDOW_ONE, H256::zero());
			}

			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 17);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::One), 4);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 33);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 1);
			RollingWindow::on_session_end();
			// session index = 2
			// Kind::Two should have been expired

			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 17);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::One), 4);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 0);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 0);
			RollingWindow::on_session_end();
			// session index = 3
			// events that happend in session 0 should have been expired

			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 5);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::One), 1);
		});
	}
}
