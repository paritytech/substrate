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

//! Communication streams for the BEEFY networking protocols.

pub mod notification;
pub mod request_response;

pub(crate) mod gossip;

pub(crate) mod beefy_protocol_name {
	/// BEEFY votes gossip protocol name suffix.
	const GOSSIP_NAME: &str = "/beefy/1";
	/// BEEFY justifications protocol name suffix.
	const JUSTIFICATIONS_NAME: &str = "/beefy/justifications/1";

	/// Old names for the gossip protocol, used for backward compatibility.
	pub(super) const LEGACY_NAMES: [&str; 1] = ["/paritytech/beefy/1"];

	/// Name of the votes gossip protocol used by BEEFY.
	///
	/// Must be registered towards the networking in order for BEEFY voter to properly function.
	pub fn gossip_protocol_name<Hash: AsRef<[u8]>>(
		genesis_hash: Hash,
		fork_id: Option<&str>,
	) -> std::borrow::Cow<'static, str> {
		if let Some(fork_id) = fork_id {
			format!("/{}/{}{}", hex::encode(genesis_hash), fork_id, GOSSIP_NAME).into()
		} else {
			format!("/{}{}", hex::encode(genesis_hash), GOSSIP_NAME).into()
		}
	}

	/// Name of the BEEFY justifications request-response protocol.
	pub fn justifications_protocol_name<Hash: AsRef<[u8]>>(
		genesis_hash: Hash,
		fork_id: Option<&str>,
	) -> std::borrow::Cow<'static, str> {
		if let Some(fork_id) = fork_id {
			format!("/{}/{}{}", hex::encode(genesis_hash), fork_id, JUSTIFICATIONS_NAME).into()
		} else {
			format!("/{}{}", hex::encode(genesis_hash), JUSTIFICATIONS_NAME).into()
		}
	}
}

/// Returns the configuration value to put in
/// [`sc_network::config::NetworkConfiguration::extra_sets`].
/// For standard protocol name see [`beefy_protocol_name::gossip_protocol_name`].
pub fn beefy_peers_set_config(
	gossip_protocol_name: std::borrow::Cow<'static, str>,
) -> sc_network::config::NonDefaultSetConfig {
	let mut cfg = sc_network::config::NonDefaultSetConfig::new(gossip_protocol_name, 1024 * 1024);

	cfg.allow_non_reserved(25, 25);
	cfg.add_fallback_names(beefy_protocol_name::LEGACY_NAMES.iter().map(|&n| n.into()).collect());
	cfg
}
