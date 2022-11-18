// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! The archive's event returned as json compatible object.

use serde::{Deserialize, Serialize};

/// The network config parameter is used when a function
/// needs to request the information from its peers.
///
/// These values can be tweaked depending on the urgency of the JSON-RPC function call.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct NetworkConfig {
	/// The total number of peers from which the information is requested.
	total_attempts: u64,
	/// The maximum number of requests to perform in parallel.
	///
	/// # Note
	///
	/// A zero value is illegal.
	max_parallel: u64,
	/// The time, in milliseconds, after which a single requests towards one peer
	/// is considered unsuccessful.
	timeout_ms: u64,
}

/// The operation could not be processed due to an error.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ErrorEvent {
	/// Reason of the error.
	pub error: String,
}

/// The result of an archive method.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct ArchiveResult<T> {
	/// Result of the method.
	pub result: T,
}

/// The event of an archive method.
#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
#[serde(tag = "event")]
pub enum ArchiveEvent<T> {
	/// The request completed successfully.
	Done(ArchiveResult<T>),
	/// The resources requested are inaccessible.
	///
	/// Resubmitting the request later might succeed.
	Inaccessible(ErrorEvent),
	/// An error occurred. This is definitive.
	Error(ErrorEvent),
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn archive_done_event() {
		let event: ArchiveEvent<String> = ArchiveEvent::Done(ArchiveResult { result: "A".into() });

		let ser = serde_json::to_string(&event).unwrap();
		let exp = r#"{"event":"done","result":"A"}"#;
		assert_eq!(ser, exp);

		let event_dec: ArchiveEvent<String> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn archive_inaccessible_event() {
		let event: ArchiveEvent<String> =
			ArchiveEvent::Inaccessible(ErrorEvent { error: "A".into() });

		let ser = serde_json::to_string(&event).unwrap();
		let exp = r#"{"event":"inaccessible","error":"A"}"#;
		assert_eq!(ser, exp);

		let event_dec: ArchiveEvent<String> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn archive_error_event() {
		let event: ArchiveEvent<String> = ArchiveEvent::Error(ErrorEvent { error: "A".into() });

		let ser = serde_json::to_string(&event).unwrap();
		let exp = r#"{"event":"error","error":"A"}"#;
		assert_eq!(ser, exp);

		let event_dec: ArchiveEvent<String> = serde_json::from_str(exp).unwrap();
		assert_eq!(event_dec, event);
	}

	#[test]
	fn archive_network_config() {
		let conf = NetworkConfig { total_attempts: 1, max_parallel: 2, timeout_ms: 3 };

		let ser = serde_json::to_string(&conf).unwrap();
		let exp = r#"{"totalAttempts":1,"maxParallel":2,"timeoutMs":3}"#;
		assert_eq!(ser, exp);

		let conf_dec: NetworkConfig = serde_json::from_str(exp).unwrap();
		assert_eq!(conf_dec, conf);
	}
}
