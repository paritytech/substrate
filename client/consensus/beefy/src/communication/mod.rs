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

//! Communication streams for the BEEFY networking protocols.

pub mod notification;
pub mod request_response;

pub(crate) mod gossip;
pub(crate) mod peers;

pub(crate) mod beefy_protocol_name {
	use array_bytes::bytes2hex;
	use sc_network::ProtocolName;

	/// BEEFY votes gossip protocol name suffix.
	const GOSSIP_NAME: &str = "/beefy/2";
	/// BEEFY justifications protocol name suffix.
	const JUSTIFICATIONS_NAME: &str = "/beefy/justifications/1";

	/// Name of the votes gossip protocol used by BEEFY.
	///
	/// Must be registered towards the networking in order for BEEFY voter to properly function.
	pub fn gossip_protocol_name<Hash: AsRef<[u8]>>(
		genesis_hash: Hash,
		fork_id: Option<&str>,
	) -> ProtocolName {
		let genesis_hash = genesis_hash.as_ref();
		if let Some(fork_id) = fork_id {
			format!("/{}/{}{}", bytes2hex("", genesis_hash), fork_id, GOSSIP_NAME).into()
		} else {
			format!("/{}{}", bytes2hex("", genesis_hash), GOSSIP_NAME).into()
		}
	}

	/// Name of the BEEFY justifications request-response protocol.
	pub fn justifications_protocol_name<Hash: AsRef<[u8]>>(
		genesis_hash: Hash,
		fork_id: Option<&str>,
	) -> ProtocolName {
		let genesis_hash = genesis_hash.as_ref();
		if let Some(fork_id) = fork_id {
			format!("/{}/{}{}", bytes2hex("", genesis_hash), fork_id, JUSTIFICATIONS_NAME).into()
		} else {
			format!("/{}{}", bytes2hex("", genesis_hash), JUSTIFICATIONS_NAME).into()
		}
	}
}

/// Returns the configuration value to put in
/// [`sc_network::config::FullNetworkConfiguration`].
/// For standard protocol name see [`beefy_protocol_name::gossip_protocol_name`].
pub fn beefy_peers_set_config(
	gossip_protocol_name: sc_network::ProtocolName,
) -> sc_network::config::NonDefaultSetConfig {
	let mut cfg = sc_network::config::NonDefaultSetConfig::new(gossip_protocol_name, 1024 * 1024);
	cfg.allow_non_reserved(25, 25);
	cfg
}

// cost scalars for reporting peers.
mod cost {
	use sc_network::ReputationChange as Rep;
	// Message that's for an outdated round.
	pub(super) const OUTDATED_MESSAGE: Rep = Rep::new(-50, "BEEFY: Past message");
	// Message that's from the future relative to our current set-id.
	pub(super) const FUTURE_MESSAGE: Rep = Rep::new(-100, "BEEFY: Future message");
	// Vote message containing bad signature.
	pub(super) const BAD_SIGNATURE: Rep = Rep::new(-100, "BEEFY: Bad signature");
	// Message received with vote from voter not in validator set.
	pub(super) const UNKNOWN_VOTER: Rep = Rep::new(-150, "BEEFY: Unknown voter");
	// A message received that cannot be evaluated relative to our current state.
	pub(super) const OUT_OF_SCOPE_MESSAGE: Rep = Rep::new(-500, "BEEFY: Out-of-scope message");
	// Message containing invalid proof.
	pub(super) const INVALID_PROOF: Rep = Rep::new(-5000, "BEEFY: Invalid commit");
	// Reputation cost per signature checked for invalid proof.
	pub(super) const PER_SIGNATURE_CHECKED: i32 = -25;
	// Reputation cost per byte for un-decodable message.
	pub(super) const PER_UNDECODABLE_BYTE: i32 = -5;
	// On-demand request was refused by peer.
	pub(super) const REFUSAL_RESPONSE: Rep = Rep::new(-100, "BEEFY: Proof request refused");
	// On-demand request for a proof that can't be found in the backend.
	pub(super) const UNKOWN_PROOF_REQUEST: Rep = Rep::new(-150, "BEEFY: Unknown proof request");
}

// benefit scalars for reporting peers.
mod benefit {
	use sc_network::ReputationChange as Rep;
	pub(super) const VOTE_MESSAGE: Rep = Rep::new(100, "BEEFY: Round vote message");
	pub(super) const KNOWN_VOTE_MESSAGE: Rep = Rep::new(50, "BEEFY: Known vote");
	pub(super) const VALIDATED_PROOF: Rep = Rep::new(100, "BEEFY: Justification");
}

#[cfg(test)]
mod tests {
	use super::*;

	use sp_core::H256;

	#[test]
	fn beefy_protocols_names() {
		use beefy_protocol_name::{gossip_protocol_name, justifications_protocol_name};
		// Create protocol name using random genesis hash.
		let genesis_hash = H256::random();
		let genesis_hex = array_bytes::bytes2hex("", genesis_hash);

		let expected_gossip_name = format!("/{}/beefy/2", genesis_hex);
		let gossip_proto_name = gossip_protocol_name(&genesis_hash, None);
		assert_eq!(gossip_proto_name.to_string(), expected_gossip_name);

		let expected_justif_name = format!("/{}/beefy/justifications/1", genesis_hex);
		let justif_proto_name = justifications_protocol_name(&genesis_hash, None);
		assert_eq!(justif_proto_name.to_string(), expected_justif_name);

		// Create protocol name using hardcoded genesis hash. Verify exact representation.
		let genesis_hash = [
			50, 4, 60, 123, 58, 106, 216, 246, 194, 188, 139, 193, 33, 212, 202, 171, 9, 55, 123,
			94, 8, 43, 12, 251, 187, 57, 173, 19, 188, 74, 205, 147,
		];
		let genesis_hex = "32043c7b3a6ad8f6c2bc8bc121d4caab09377b5e082b0cfbbb39ad13bc4acd93";

		let expected_gossip_name = format!("/{}/beefy/2", genesis_hex);
		let gossip_proto_name = gossip_protocol_name(&genesis_hash, None);
		assert_eq!(gossip_proto_name.to_string(), expected_gossip_name);

		let expected_justif_name = format!("/{}/beefy/justifications/1", genesis_hex);
		let justif_proto_name = justifications_protocol_name(&genesis_hash, None);
		assert_eq!(justif_proto_name.to_string(), expected_justif_name);
	}
}
