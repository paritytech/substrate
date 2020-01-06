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

//! Substrate core types and inherents for timestamps.

#![cfg_attr(not(feature = "std"), no_std)]

use codec::Encode;
#[cfg(feature = "std")]
use codec::Decode;
#[cfg(feature = "std")]
use sp_inherents::ProvideInherentData;
#[cfg(feature = "std")]
use log::trace;
use sp_inherents::{InherentIdentifier, IsFatalError, InherentData};

use sp_runtime::RuntimeString;

/// The identifier for the `timestamp` inherent.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"timstap0";
/// The type of the inherent.
pub type InherentType = u64;

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
		use std::time::SystemTime;

		let now = SystemTime::now();
		now.duration_since(SystemTime::UNIX_EPOCH)
			.map_err(|_| {
				"Current time is before unix epoch".into()
			}).and_then(|d| {
				let timestamp: InherentType = d.as_millis() as u64;

				// KUSAMA HOTFIX: mutate timestamp to make it revert back in time and have slots
				// happen at 6x their speed from then until we have caught up with the present time.

				const REVIVE_TIMESTAMP: u64 = 1578387600000;
				const FORK_TIMESTAMP: u64 = 1578139812 * 1000;
				const WARP_FACTOR: u64 = 6;

				let time_since_revival = timestamp.saturating_sub(REVIVE_TIMESTAMP);
				let warped_timestamp = FORK_TIMESTAMP + WARP_FACTOR * time_since_revival;

				trace!(target: "babe", "timestamp warped: {:?} to {:?} ({:?} since revival)", timestamp, warped_timestamp, time_since_revival);

				// we want to ensure our timestamp is such that slots run monotonically with blocks
				// at 1/6th of the slot_duration from this slot onwards until we catch up to the
				// wall-clock time.
				let timestamp = timestamp.min(warped_timestamp);

				inherent_data.put_data(INHERENT_IDENTIFIER, &timestamp)
			})
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		InherentError::try_from(&INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}


/// A trait which is called when the timestamp is set.
#[impl_trait_for_tuples::impl_for_tuples(30)]
pub trait OnTimestampSet<Moment> {
	fn on_timestamp_set(moment: Moment);
}
