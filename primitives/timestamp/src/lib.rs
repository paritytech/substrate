// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};
use sp_inherents::{InherentData, InherentIdentifier, IsFatalError};
use sp_std::time::Duration;

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

	/// Returns `self` as [`Duration`].
	pub const fn as_duration(self) -> Duration {
		Duration::from_millis(self.0)
	}

	/// Returns `self` as a `u64` representing the elapsed time since the UNIX_EPOCH in
	/// milliseconds.
	pub const fn as_millis(&self) -> u64 {
		self.0
	}

	/// Checked subtraction that returns `None` on an underflow.
	pub fn checked_sub(self, other: Self) -> Option<Self> {
		self.0.checked_sub(other.0).map(Self)
	}

	/// The current timestamp using the system time.
	#[cfg(feature = "std")]
	pub fn current() -> Self {
		use std::time::SystemTime;

		let now = SystemTime::now();
		now.duration_since(SystemTime::UNIX_EPOCH)
			.expect("Current time is always after unix epoch; qed")
			.into()
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

impl From<Duration> for Timestamp {
	fn from(duration: Duration) -> Self {
		Timestamp(duration.as_millis() as u64)
	}
}

/// Errors that can occur while checking the timestamp inherent.
#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode, thiserror::Error))]
pub enum InherentError {
	/// The time between the blocks is too short.
	#[cfg_attr(
		feature = "std",
		error("The time since the last timestamp is lower than the minimum period.")
	)]
	TooEarly,
	/// The block timestamp is too far in the future
	#[cfg_attr(feature = "std", error("The timestamp of the block is too far in the future."))]
	TooFarInFuture,
}

impl IsFatalError for InherentError {
	fn is_fatal_error(&self) -> bool {
		match self {
			InherentError::TooEarly => true,
			InherentError::TooFarInFuture => true,
		}
	}
}

impl InherentError {
	/// Try to create an instance ouf of the given identifier and data.
	#[cfg(feature = "std")]
	pub fn try_from(id: &InherentIdentifier, mut data: &[u8]) -> Option<Self> {
		if id == &INHERENT_IDENTIFIER {
			<InherentError as codec::Decode>::decode(&mut data).ok()
		} else {
			None
		}
	}
}

/// Auxiliary trait to extract timestamp inherent data.
pub trait TimestampInherentData {
	/// Get timestamp inherent data.
	fn timestamp_inherent_data(&self) -> Result<Option<InherentType>, sp_inherents::Error>;
}

impl TimestampInherentData for InherentData {
	fn timestamp_inherent_data(&self) -> Result<Option<InherentType>, sp_inherents::Error> {
		self.get_data(&INHERENT_IDENTIFIER)
	}
}

/// Provide duration since unix epoch in millisecond for timestamp inherent.
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	max_drift: InherentType,
	timestamp: InherentType,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	/// Create `Self` while using the system time to get the timestamp.
	pub fn from_system_time() -> Self {
		Self {
			max_drift: std::time::Duration::from_secs(60).into(),
			timestamp: Timestamp::current(),
		}
	}

	/// Create `Self` using the given `timestamp`.
	pub fn new(timestamp: InherentType) -> Self {
		Self { max_drift: std::time::Duration::from_secs(60).into(), timestamp }
	}

	/// With the given maximum drift.
	///
	/// By default the maximum drift is 60 seconds.
	///
	/// The maximum drift is used when checking the inherents of a runtime. If the current timestamp
	/// plus the maximum drift is smaller than the timestamp in the block, the block will be
	/// rejected as being too far in the future.
	pub fn with_max_drift(mut self, max_drift: std::time::Duration) -> Self {
		self.max_drift = max_drift.into();
		self
	}

	/// Returns the timestamp of this inherent data provider.
	pub fn timestamp(&self) -> InherentType {
		self.timestamp
	}
}

#[cfg(feature = "std")]
impl sp_std::ops::Deref for InherentDataProvider {
	type Target = InherentType;

	fn deref(&self) -> &Self::Target {
		&self.timestamp
	}
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	async fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), sp_inherents::Error> {
		inherent_data.put_data(INHERENT_IDENTIFIER, &self.timestamp)
	}

	async fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> Option<Result<(), sp_inherents::Error>> {
		Some(Err(sp_inherents::Error::Application(Box::from(InherentError::try_from(
			identifier, error,
		)?))))
	}
}
