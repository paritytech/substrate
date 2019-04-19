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

use parity_codec as codec;

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct Timestamp(u64);

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
pub struct Duration(u64);

#[derive(Clone, Copy, PartialEq, Eq, Ord, PartialOrd)]
#[derive(codec::Encode, codec::Decode)]
pub enum RequestStatus {
	Unknown,
	Finished(u16),
}

impl Default for RequestStatus {
	fn default() -> Self {
		RequestStatus::Unknown
	}
}

impl RequestStatus {
	pub fn from_u16(status: u16) -> Option<Self> {
		match status {
			0 => Some(RequestStatus::Unknown),
			100...999 => Some(RequestStatus::Finished(status)),
			_ => None,
		}
	}
}

impl Timestamp {
	// TODO [ToDr] More ops
	pub fn add(&self, duration: Duration) -> Timestamp {
		Timestamp(self.0.saturating_add(duration.0))
	}
}

/// Opaque type for offchain http requests.
#[derive(Clone, Copy)]
pub struct RequestId(u16);

