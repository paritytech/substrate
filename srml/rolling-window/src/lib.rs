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
	StorageValue, StorageMap, decl_module, decl_storage,
};

type Kind = u32;
type Window = u32;

pub trait Trait: system::Trait {}

decl_storage! {
	trait Store for Module<T: Trait> as Example {
		/// Misbehavior reports
		MisconductReports get(kind): map Kind => Vec<(u32, T::Hash)>;

		/// Rolling window length for different kinds
		WindowLength get(w) config(): map Kind => Window;

		/// Session index
		pub SessionIndex get(s) config(): u32 = 0;

		/// The number of different kinds
		NumberOfKinds get(k) config(): u32 = 0;
	}
}

decl_module! {
	/// Simple declaration of the `Module` type. Lets the macro know what its working on.
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {}
}

impl<T: Trait> Module<T> {
	/// On startup make sure no misconducts are reported
	pub fn on_initialize<K: Into<u32> + Copy>(kinds: &[(K, u32)]) {
		NumberOfKinds::put(kinds.len() as u32);

		for (kind, window_length) in kinds {
			WindowLength::insert(kind.clone().into(), window_length);
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

		for kind in 0..NumberOfKinds::get() {
			<MisconductReports<T>>::mutate(kind, |window| {
				let w = WindowLength::get(kind);

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

	/// Report misbehaviour for a misconduct kind
	///
	/// Return number of misbehaviors in the current window which
	/// may include duplicated misbehaviour from a validator
	pub fn report_misbehavior<K: Into<u32>>(kind: K, footprint: T::Hash) -> u64 {
		let session = SessionIndex::get();
		let kind: u32 = kind.into();

		if <MisconductReports<T>>::exists(kind) {
			<MisconductReports<T>>::mutate(kind, |w| w.push((session, footprint)));
		} else {
			<MisconductReports<T>>::insert(kind, vec![(session, footprint)]);
		}
		Self::get_misbehavior(kind)
	}


	pub fn get_misbehavior<K: Into<u32>>(kind: K) -> u64 {
		<MisconductReports<T>>::get(kind.into()).len() as u64
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
			.validator_count(50)
			.num_validators(50)
			.build(),
		|| {

			let kinds = vec![(0, 4), (1, 3), (2, 1)];

			RollingWindow::on_initialize(&kinds);

			for i in 1..=10 {
				let hash = H256::random();
				assert_eq!(i, RollingWindow::report_misbehavior(0, hash));
			}

			for i in 1..=4 {
				let hash = H256::random();
				assert_eq!(i, RollingWindow::report_misbehavior(1, hash));
			}

			RollingWindow::on_session_end();
			// session = 1
			assert_eq!(RollingWindow::get_misbehavior(0), 10);
			assert_eq!(RollingWindow::get_misbehavior(1), 4);

			RollingWindow::on_session_end();
			// session = 2
			assert_eq!(RollingWindow::get_misbehavior(0), 10);
			assert_eq!(RollingWindow::get_misbehavior(1), 4);

			RollingWindow::on_session_end();
			// session = 3
			assert_eq!(RollingWindow::get_misbehavior(0), 10);
			assert_eq!(RollingWindow::get_misbehavior(1), 0);

			RollingWindow::on_session_end();
			// session = 4
			assert_eq!(RollingWindow::get_misbehavior(0), 0);
			assert_eq!(RollingWindow::get_misbehavior(1), 0);

		});
	}
}
