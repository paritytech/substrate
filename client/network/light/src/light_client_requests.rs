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

//! Helpers for outgoing and incoming light client requests.

/// For incoming light client requests.
pub mod handler;

use sc_network_common::{config::ProtocolId, request_responses::ProtocolConfig};

use std::time::Duration;

/// Generate the light client protocol name from the genesis hash and fork id.
fn generate_protocol_name<Hash: AsRef<[u8]>>(genesis_hash: Hash, fork_id: Option<&str>) -> String {
	let genesis_hash = genesis_hash.as_ref();
	if let Some(fork_id) = fork_id {
		format!("/{}/{}/light/2", array_bytes::bytes2hex("", genesis_hash), fork_id)
	} else {
		format!("/{}/light/2", array_bytes::bytes2hex("", genesis_hash))
	}
}

/// Generate the legacy light client protocol name from chain specific protocol identifier.
fn generate_legacy_protocol_name(protocol_id: &ProtocolId) -> String {
	format!("/{}/light/2", protocol_id.as_ref())
}

/// Generates a [`ProtocolConfig`] for the light client request protocol, refusing incoming
/// requests.
pub fn generate_protocol_config<Hash: AsRef<[u8]>>(
	protocol_id: &ProtocolId,
	genesis_hash: Hash,
	fork_id: Option<&str>,
) -> ProtocolConfig {
	ProtocolConfig {
		name: generate_protocol_name(genesis_hash, fork_id).into(),
		fallback_names: std::iter::once(generate_legacy_protocol_name(protocol_id).into())
			.collect(),
		max_request_size: 1 * 1024 * 1024,
		max_response_size: 16 * 1024 * 1024,
		request_timeout: Duration::from_secs(15),
		inbound_queue: None,
	}
}
