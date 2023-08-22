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

use clap::Args;
use sp_core::H256;
use std::str::FromStr;

fn parse_kx_secret(s: &str) -> Result<[u8; 32], String> {
	H256::from_str(s).map(H256::to_fixed_bytes).map_err(|err| err.to_string())
}

/// Parameters used to create the mixnet configuration.
#[derive(Debug, Clone, Args)]
pub struct MixnetParams {
	/// Enable the mixnet service.
	///
	/// This will make the mixnet RPC methods available. If the node is running as a validator, it
	/// will also attempt to register and operate as a mixnode.
	#[arg(long)]
	pub mixnet: bool,

	/// The mixnet key-exchange secret to use in session 0.
	///
	/// Should be 64 hex characters, giving a 32-byte secret.
	///
	/// WARNING: Secrets provided as command-line arguments are easily exposed. Use of this option
	/// should be limited to development and testing.
	#[arg(long, value_name = "SECRET", value_parser = parse_kx_secret)]
	pub mixnet_session_0_kx_secret: Option<[u8; 32]>,
}

impl MixnetParams {
	/// Returns the mixnet configuration, or `None` if the mixnet is disabled.
	pub fn config(&self, is_authority: bool) -> Option<sc_mixnet::Config> {
		self.mixnet.then(|| {
			let mut config = sc_mixnet::Config {
				core: sc_mixnet::CoreConfig {
					session_0_kx_secret: self.mixnet_session_0_kx_secret,
					..Default::default()
				},
				..Default::default()
			};
			if !is_authority {
				// Only authorities can be mixnodes; don't attempt to register
				config.substrate.register = false;
				// Only mixnodes need to allow connections from non-mixnodes
				config.substrate.num_gateway_slots = 0;
			}
			config
		})
	}
}
