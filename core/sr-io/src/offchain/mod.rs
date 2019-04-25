// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! A collection of higher lever helpers for offchain workers.

pub mod http;

/// Opaque timestamp type
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Timestamp(pub(crate) u64);

/// Duration type
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Duration(pub(crate) u64);

impl Duration {
	/// Create new duration representing given number of milliseconds.
	pub fn from_millis(millis: u64) -> Self {
		Duration(millis)
	}

	/// Returns number of milliseconds this Duration represents.
	pub fn millis(&self) -> u64 {
		self.0
	}
}

impl Timestamp {
	/// Increase the timestamp by given `Duration`.
	pub fn add(&self, duration: Duration) -> Timestamp {
		Timestamp(self.0.saturating_add(duration.0))
	}

	/// Decrease the timestamp by given `Duration`
	pub fn sub(&self, duration: Duration) -> Timestamp {
		Timestamp(self.0.saturating_sub(duration.0))
	}

	/// Returns a saturated difference (Duration) between two Timestamps.
	pub fn diff(&self, other: &Self) -> Duration {
		Duration(self.0.saturating_sub(other.0))
	}

	/// Return number of milliseconds since UNIX epoch.
	pub fn unix_millis(&self) -> u64 {
		self.0
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn timestamp_ops() {
		let t = Timestamp(5);
		assert_eq!(t.add(Duration::from_millis(10)), Timestamp(15));
		assert_eq!(t.sub(Duration::from_millis(10)), Timestamp(0));
		assert_eq!(t.diff(&Timestamp(3)), Duration(2));
	}
}
