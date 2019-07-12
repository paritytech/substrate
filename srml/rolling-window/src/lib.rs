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

//! # noooo docs
//!

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(test)]
mod mock;

use srml_support::{
	StorageValue, StorageMap, EnumerableStorageMap, decl_module, decl_storage,
};
use parity_codec::Codec;
use sr_primitives::traits::MaybeSerializeDebug;

type Window = u32;
type Session = u32;

pub trait Trait: system::Trait {
	type Kind: Copy + Clone + Codec + MaybeSerializeDebug;
}

decl_storage! {
	trait Store for Module<T: Trait> as RollingWindow {
		/// Misbehavior reports
		///
		/// It maps each kind into an unique hash and the session number for the misconduct
		MisconductReports get(kind): linked_map T::Kind => Vec<(Session, T::Hash)>;

		/// Rolling window length for different kinds
		///
		/// Each kind has its own window length
		WindowLength get(w) config(): linked_map T::Kind => Window;

		/// Session index
		SessionIndex get(s) config(): u32 = 0;
	}
}

decl_module! {
	/// Rolling Window module
	///
	/// It is similar to a `simple moving average` except that it just
	/// return the number of misbehaviors in the window instead of calculating the average
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {
	/// On startup initialize all kinds
	///
	/// Make sure that all kinds is unique otherwise
	/// a kind may be overwritten by another kind
	///
	/// Panics if length is bigger than `u32::max_value()`
	pub fn on_initialize(kinds: Vec<(T::Kind, Window)>) {
		assert!(kinds.len() <= u32::max_value() as usize);

		for (kind, window_length) in kinds {
			<WindowLength::<T>>::insert(kind, window_length);
		}
	}

	/// Remove items that doesn't fit into the rolling window
	pub fn on_session_end() {
		let mut session_wrapped = false;

		let session = match SessionIndex::get().checked_add(1) {
			Some(v) => v,
			None => {
				session_wrapped = true;
				0
			}
		};

		// fixme possible iterator invalidation
		for (kind, _) in <MisconductReports<T>>::enumerate() {
			<MisconductReports<T>>::mutate(kind, |window| {
				let w = <WindowLength<T>>::get(kind);

				// it is guaranteed that `s` happend before `session`
				window.retain(|(s, _)| {

					let window_wrapped = s.checked_add(w).is_none();
					let x = s.wrapping_add(w);

					match (session_wrapped, window_wrapped) {
						(false, true) => true,
						(true, false) => false,
						(true, true) | (false, false) if x > session => true,
						_ => false
					}
				});
			});
		}

		SessionIndex::put(session);
	}

	/// Report misbehaviour for a kind
	pub fn report_misbehavior(kind: T::Kind, footprint: T::Hash) {
		let session = SessionIndex::get();

		if <MisconductReports<T>>::exists(kind) {
			<MisconductReports<T>>::mutate(kind, |w| w.push((session, footprint)));
		} else {
			<MisconductReports<T>>::insert(kind, vec![(session, footprint)]);
		}
	}

	/// Return number of misbehaviors in the current window which
	/// may include duplicated misbehaviours
	pub fn get_misbehaved(kind: T::Kind) -> u64 {
		<MisconductReports<T>>::get(kind).len() as u64
	}


	/// Return number of misbehaviors in the current window which
	/// may include duplicated misbehaviours
	pub fn get_misbehaved_unique(kind: T::Kind) -> u64 {
		let window = <MisconductReports<T>>::get(kind);

		let mut seen_ids = rstd::vec::Vec::new();
		let mut unique = 0;
		// session can never be smaller than 0
		let mut last_session = 0;

		for (session, id) in window {
			// new session reset `seem_ids`
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

			let kinds = vec![(Kind::One, 4), (Kind::Two, 3)];

			RollingWindow::on_initialize(kinds);

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
			let kinds = vec![(Kind::One, 3), (Kind::Two, 2)];
			RollingWindow::on_initialize(kinds);

			let one: H256 = [1_u8; 32].into();
			let two: H256 = [2_u8; 32].into();

			for _ in 0..10 {
				RollingWindow::report_misbehavior(Kind::One, H256::zero());
			}

			for _ in 0..33 {
				RollingWindow::report_misbehavior(Kind::Two, H256::zero());
			}

			RollingWindow::report_misbehavior(Kind::One, one);
			RollingWindow::report_misbehavior(Kind::One, two);

			assert_eq!(RollingWindow::get_misbehaved(Kind::One), 12);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::One), 3);
			assert_eq!(RollingWindow::get_misbehaved(Kind::Two), 33);
			assert_eq!(RollingWindow::get_misbehaved_unique(Kind::Two), 1);
			RollingWindow::on_session_end();
			// session index = 1

			for _ in 0..5 {
				RollingWindow::report_misbehavior(Kind::One, H256::zero());
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
