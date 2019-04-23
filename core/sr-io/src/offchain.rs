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

use parity_codec as codec;

/// Opaque timestamp type
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct Timestamp(pub(crate) u64);

/// Duration type
#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
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

/// HTTP utilities
pub mod http {
	use super::*;

	/// Status of the HTTP request
	#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
	#[derive(codec::Encode, codec::Decode)]
	pub enum RequestStatus {
		/// Request status of this ID is not known.
		Unknown,
		/// The request is finished with given status code.
		Finished(u16),
	}

	impl Default for RequestStatus {
		fn default() -> Self {
			RequestStatus::Unknown
		}
	}

	impl RequestStatus {
		/// Parse u16 as `RequestStatus`.
		///
		/// The first hundred of codes indicate internal states.
		/// The rest are http response status codes.
		pub fn from_u16(status: u16) -> Option<Self> {
			match status {
				0 => Some(RequestStatus::Unknown),
				100...999 => Some(RequestStatus::Finished(status)),
				_ => None,
			}
		}
	}

	/// Opaque type for offchain http requests.
	#[derive(Clone, Copy)]
	pub struct RequestId(pub(crate) u16);

	/// An HTTP request builder.
	#[derive(Default)]
	pub struct Request {

	}
}

#[cfg(test)]
mod tests {

	#[test]
	fn timestamp_ops() {
		let t = Timestamp(5);
		assert_eq!(t.add(Duration::from_millis(10)), Timestamp(15));
		assert_eq!(t.sub(Duration::from_millis(10)), Timestamp(0));
		assert_eq!(t.diff(&Timestamp(3)), Duration(2));
	}
}
