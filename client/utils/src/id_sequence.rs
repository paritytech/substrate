// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Produce opaque sequential IDs.

/// A Sequence of IDs.
#[derive(Debug, Default)]
// The `Clone` trait is intentionally not defined on this type.
pub struct IDSequence {
	next_id: u64,
}

/// A Sequential ID.
///
/// Its integer value is intentionally not public: it is supposed to be instantiated from within
/// this module only.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct SeqID(u64);

impl std::fmt::Display for SeqID {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl IDSequence {
	/// Create a new ID-sequence.
	pub fn new() -> Self {
		Default::default()
	}

	/// Obtain another ID from this sequence.
	pub fn next_id(&mut self) -> SeqID {
		let id = SeqID(self.next_id);
		self.next_id += 1;

		id
	}
}
