// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Substrate core types and inherents for timestamps.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, Decode};
#[cfg(feature = "std")]
use sp_inherents::ProvideInherentData;
use sp_inherents::{InherentIdentifier, IsFatalError, InherentData};

use sp_runtime::RuntimeString;

/// The identifier for the `timestamp` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"timstap0";

/// The type of the inherent.
pub type InherentType = Timestamp;

/// Unit type wrapper that represents a timestamp.
///
/// Such a timestamp is the time since the UNIX_EPOCH in milliseconds at a given point in time.
#[derive(Debug, Encode, Decode, Eq, Clone, Copy, Default, Ord)]
pub struct Timestamp(u64);

impl Timestamp {
	/// Create new `Self`.
	pub const fn new(inner: u64) -> Self {
		Self(inner)
	}
}

impl sp_std::ops::Deref for Timestamp {
	type Target = u64;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl core::ops::Add for Timestamp {
	type Output = Self;

	fn add(self, other: Self) -> Self {
		Self(self.0 + other.0)
	}
}

impl core::ops::Add<u64> for Timestamp {
	type Output = Self;

	fn add(self, other: u64) -> Self {
		Self(self.0 + other)
	}
}

impl<T: Into<u64> + Copy> core::cmp::PartialEq<T> for Timestamp {
	fn eq(&self, eq: &T) -> bool {
		self.0 == (*eq).into()
	}
}

impl<T: Into<u64> + Copy> core::cmp::PartialOrd<T> for Timestamp {
	fn partial_cmp(&self, other: &T) -> Option<core::cmp::Ordering> {
		self.0.partial_cmp(&(*other).into())
	}
}

#[cfg(feature = "std")]
impl std::fmt::Display for Timestamp {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl From<u64> for Timestamp {
	fn from(timestamp: u64) -> Self {
		Timestamp(timestamp)
	}
}

impl From<Timestamp> for u64 {
	fn from(timestamp: Timestamp) -> u64 {
		timestamp.0
	}
}

impl From<sp_std::time::Duration> for Timestamp {
	fn from(duration: sp_std::time::Duration) -> Self {
		Timestamp(duration.as_millis() as u64)
	}
}

/// Errors that can occur while checking the timestamp inherent.
#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum InherentError {
	/// The timestamp is valid in the future.
	/// This is a non-fatal-error and will not stop checking the inherents.
	ValidAtTimestamp(InherentType),
	/// Some other error.
	Other(RuntimeString),
}

impl IsFatalError for InherentError {
	fn is_fatal_error(&self) -> bool {
		match self {
			InherentError::ValidAtTimestamp(_) => false,
			InherentError::Other(_) => true,
		}
	}
}

impl InherentError {
	/// Try to create an instance ouf of the given identifier and data.
	#[cfg(feature = "std")]
	pub fn try_from(id: &InherentIdentifier, data: &[u8]) -> Option<Self> {
		if id == &INHERENT_IDENTIFIER {
			<InherentError as codec::Decode>::decode(&mut &data[..]).ok()
		} else {
			None
		}
	}
}

/// Auxiliary trait to extract timestamp inherent data.
pub trait TimestampInherentData {
	/// Get timestamp inherent data.
	fn timestamp_inherent_data(&self) -> Result<InherentType, sp_inherents::Error>;
}

impl TimestampInherentData for InherentData {
	fn timestamp_inherent_data(&self) -> Result<InherentType, sp_inherents::Error> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "Timestamp inherent data not found".into()))
	}
}

/// Provide duration since unix epoch in millisecond for timestamp inherent.
#[cfg(feature = "std")]
pub struct InherentDataProvider;

#[cfg(feature = "std")]
impl ProvideInherentData for InherentDataProvider {
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), sp_inherents::Error> {
		use wasm_timer::SystemTime;

		let now = SystemTime::now();
		now.duration_since(SystemTime::UNIX_EPOCH)
			.map_err(|_| {
				"Current time is before unix epoch".into()
			}).and_then(|d| {
				inherent_data.put_data(INHERENT_IDENTIFIER, &InherentType::from(d))
			})
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		InherentError::try_from(&INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}

