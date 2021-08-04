// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
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

use libp2p::Multiaddr;
use serde::{Deserialize, Deserializer, Serialize};

/// List of telemetry servers we want to talk to. Contains the URL of the server, and the
/// maximum verbosity level.
///
/// The URL string can be either a URL or a multiaddress.
#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub struct TelemetryEndpoints(
	#[serde(deserialize_with = "url_or_multiaddr_deser")] pub(crate) Vec<(Multiaddr, u8)>,
);

/// Custom deserializer for TelemetryEndpoints, used to convert urls or multiaddr to multiaddr.
fn url_or_multiaddr_deser<'de, D>(deserializer: D) -> Result<Vec<(Multiaddr, u8)>, D::Error>
where
	D: Deserializer<'de>,
{
	Vec::<(String, u8)>::deserialize(deserializer)?
		.iter()
		.map(|e| url_to_multiaddr(&e.0).map_err(serde::de::Error::custom).map(|m| (m, e.1)))
		.collect()
}

impl TelemetryEndpoints {
	/// Create a `TelemetryEndpoints` based on a list of `(String, u8)`.
	pub fn new(endpoints: Vec<(String, u8)>) -> Result<Self, libp2p::multiaddr::Error> {
		let endpoints: Result<Vec<(Multiaddr, u8)>, libp2p::multiaddr::Error> =
			endpoints.iter().map(|e| Ok((url_to_multiaddr(&e.0)?, e.1))).collect();
		endpoints.map(Self)
	}
}

impl TelemetryEndpoints {
	/// Return `true` if there are no telemetry endpoints, `false` otherwise.
	pub fn is_empty(&self) -> bool {
		self.0.is_empty()
	}
}

/// Parses a WebSocket URL into a libp2p `Multiaddr`.
fn url_to_multiaddr(url: &str) -> Result<Multiaddr, libp2p::multiaddr::Error> {
	// First, assume that we have a `Multiaddr`.
	let parse_error = match url.parse() {
		Ok(ma) => return Ok(ma),
		Err(err) => err,
	};

	// If not, try the `ws://path/url` format.
	if let Ok(ma) = libp2p::multiaddr::from_url(url) {
		return Ok(ma)
	}

	// If we have no clue about the format of that string, assume that we were expecting a
	// `Multiaddr`.
	Err(parse_error)
}

#[cfg(test)]
mod tests {
	use super::{url_to_multiaddr, TelemetryEndpoints};
	use libp2p::Multiaddr;

	#[test]
	fn valid_endpoints() {
		let endp = vec![
			("wss://telemetry.polkadot.io/submit/".into(), 3),
			("/ip4/80.123.90.4/tcp/5432".into(), 4),
		];
		let telem =
			TelemetryEndpoints::new(endp.clone()).expect("Telemetry endpoint should be valid");
		let mut res: Vec<(Multiaddr, u8)> = vec![];
		for (a, b) in endp.iter() {
			res.push((url_to_multiaddr(a).expect("provided url should be valid"), *b))
		}
		assert_eq!(telem.0, res);
	}

	#[test]
	fn invalid_endpoints() {
		let endp = vec![
			("/ip4/...80.123.90.4/tcp/5432".into(), 3),
			("/ip4/no:!?;rlkqre;;::::///tcp/5432".into(), 4),
		];
		let telem = TelemetryEndpoints::new(endp);
		assert!(telem.is_err());
	}

	#[test]
	fn valid_and_invalid_endpoints() {
		let endp = vec![
			("/ip4/80.123.90.4/tcp/5432".into(), 3),
			("/ip4/no:!?;rlkqre;;::::///tcp/5432".into(), 4),
		];
		let telem = TelemetryEndpoints::new(endp);
		assert!(telem.is_err());
	}
}
