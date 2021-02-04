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

use codec::Encode;
#[cfg(feature = "std")]
use codec::Decode;
use sp_inherents::{InherentIdentifier, IsFatalError, InherentData};

use sp_runtime::RuntimeString;

/// The identifier for the `timestamp` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"timstap0";
/// The type of the inherent.
pub type InherentType = u64;

/// Errors that can occur while checking the timestamp inherent.
#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode, thiserror::Error))]
pub enum InherentError {
	/// The timestamp is valid in the future.
	/// This is a non-fatal-error and will not stop checking the inherents.
	#[cfg_attr(feature = "std", error("Block will be valid at {0}."))]
	ValidAtTimestamp(InherentType),
	/// Some other error.
	#[cfg_attr(feature = "std", error("Some other error {0}."))]
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

/// The current timestamp using the system time.
///
/// This timestamp is the time since the UNIX epoch.
#[cfg(feature = "std")]
fn current_timestamp() -> std::time::Duration {
	use wasm_timer::SystemTime;

	let now = SystemTime::now();
	now.duration_since(SystemTime::UNIX_EPOCH)
		.expect("Current time is always after unix epoch; qed")
}

/// Provide duration since unix epoch in millisecond for timestamp inherent.
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	max_drift: std::time::Duration,
	timestamp: std::time::Duration,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	/// Create `Self` while using the system time to get the timestamp.
	pub fn from_system_time() -> Self {
		Self {
			max_drift: std::time::Duration::from_secs(60),
			timestamp: current_timestamp(),
		}
	}

	/// With the given maximum drift.
	///
	/// By default the maximum drift is 60 seconds.
	///
	/// The maximum drift is used when checking the inherents of a runtime. If the current timestamp
	/// plus the maximum drift is smaller than the timestamp in the block, the block will be rejected
	/// as being too far in the future.
	pub fn with_max_drift(mut self, max_drift: std::time::Duration) -> Self {
		self.max_drift = max_drift;
		self
	}

	/// Returns the timestamp of this inherent data provider.
	pub fn timestamp(&self) -> std::time::Duration {
		self.timestamp
	}
}

#[cfg(feature = "std")]
impl sp_inherents::InherentDataProvider for InherentDataProvider {
	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), sp_inherents::Error> {
		let duration: InherentType = self.timestamp.as_millis() as u64;
		inherent_data.put_data(INHERENT_IDENTIFIER, &duration)
	}

	fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> sp_inherents::TryHandleErrorResult {
		if *identifier != INHERENT_IDENTIFIER {
			return None
		}

		match InherentError::try_from(&INHERENT_IDENTIFIER, error) {
			Some(InherentError::ValidAtTimestamp(valid)) => {
				let max_drift = self.max_drift;
				let timestamp = self.timestamp;
				let fut = async move {
					let valid = std::time::Duration::from_millis(valid);
					// halt import until timestamp is valid.
					// reject when too far ahead.
					if valid > timestamp + max_drift {
						return Err(Box::from(String::from("Too far in future")))
					}

					let diff = valid.checked_sub(timestamp).unwrap_or_default();
					log::info!(
						target: "timestamp",
						"halting for block {} milliseconds in the future",
						diff.as_millis(),
					);

					futures_timer::Delay::new(diff).await;

					Ok(())
				};
				Some(Box::pin(fut))
			},
			Some(InherentError::Other(o)) => {
				Some(Box::pin(async move { Err(Box::from(String::from(o))) }))
			},
			None => None
		}
	}
}


/// A trait which is called when the timestamp is set.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait OnTimestampSet<Moment> {
	fn on_timestamp_set(moment: Moment);
}
