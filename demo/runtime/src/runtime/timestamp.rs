// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Timestamp manager: just handles the current timestamp.

use runtime_support::storage::StorageValue;
use runtime::staking::PublicPass;

pub type Timestamp = u64;

storage_items! {
	pub Now: b"tim:val" => required Timestamp;
}

impl_dispatch! {
	pub mod public;
	fn set(now: Timestamp) = 0;
}

impl<'a> public::Dispatch for PublicPass<'a> {
	/// Set the current time.
	fn set(self, now: Timestamp) {
		Now::put(&now);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::public::*;

	use runtime_io::{with_externalities, twox_128, TestExternalities};
	use runtime_support::storage::StorageValue;
	use runtime::timestamp;
	use codec::{Joiner, KeyedVec};
	use demo_primitives::AccountId;
	use runtime::staking::PublicPass;

	#[test]
	fn timestamp_works() {
		let mut t: TestExternalities = map![
			twox_128(Now::key()).to_vec() => vec![].and(&42u64)
		];

		with_externalities(&mut t, || {
			assert_eq!(Now::get(), 42);
			PublicPass::nobody().set(69);
			assert_eq!(Now::get(), 69);
		});
	}
}
