// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Timestamp manager: just handles the current timestamp.

use support::storage;

const CURRENT_TIMESTAMP: &[u8] = b"tim:val";

/// Representation of a time.
pub type Timestamp = u64;

/// Get the current time.
pub fn get() -> Timestamp {
	storage::get_or_default(CURRENT_TIMESTAMP)
}

pub mod public {
	use super::*;

	/// Set the current time.
	pub fn set(now: Timestamp) {
		storage::put(CURRENT_TIMESTAMP, &now);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use super::public::*;

	use runtime_std::{with_externalities, twox_128, TestExternalities};
	use runtime::timestamp;
	use codec::{Joiner, KeyedVec};

	#[test]
	fn timestamp_works() {
		let mut t = TestExternalities { storage: map![
			twox_128(CURRENT_TIMESTAMP).to_vec() => vec![].join(&42u64)
		], };

		with_externalities(&mut t, || {
			assert_eq!(get(), 42);
			set(69);
			assert_eq!(get(), 69);
		});
	}
}
