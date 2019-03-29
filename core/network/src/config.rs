// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Configuration for the networking layer of Substrate.

pub use network_libp2p::{NonReservedPeerMode, NetworkConfiguration, NodeKeyConfig, Secret};

use bitflags::bitflags;
use crate::chain::Client;
use parity_codec;
use crate::on_demand::OnDemandService;
use runtime_primitives::traits::{Block as BlockT};
use crate::service::{ExHashT, TransactionPool};
use std::sync::Arc;

/// Service initialization parameters.
pub struct Params<B: BlockT, S, H: ExHashT> {
	/// Configuration.
	pub config: ProtocolConfig,
	/// Network layer configuration.
	pub network_config: NetworkConfiguration,
	/// Substrate relay chain access point.
	pub chain: Arc<Client<B>>,
	/// On-demand service reference.
	pub on_demand: Option<Arc<OnDemandService<B>>>,
	/// Transaction pool.
	pub transaction_pool: Arc<TransactionPool<H, B>>,
	/// Protocol specialization.
	pub specialization: S,
}

/// Configuration for the Substrate-specific part of the networking layer.
#[derive(Clone)]
pub struct ProtocolConfig {
	/// Assigned roles.
	pub roles: Roles,
}

impl Default for ProtocolConfig {
	fn default() -> ProtocolConfig {
		ProtocolConfig {
			roles: Roles::FULL,
		}
	}
}

bitflags! {
	/// Bitmask of the roles that a node fulfills.
	pub struct Roles: u8 {
		/// No network.
		const NONE = 0b00000000;
		/// Full node, does not participate in consensus.
		const FULL = 0b00000001;
		/// Light client node.
		const LIGHT = 0b00000010;
		/// Act as an authority
		const AUTHORITY = 0b00000100;
	}
}

impl parity_codec::Encode for Roles {
	fn encode_to<T: parity_codec::Output>(&self, dest: &mut T) {
		dest.push_byte(self.bits())
	}
}

impl parity_codec::Decode for Roles {
	fn decode<I: parity_codec::Input>(input: &mut I) -> Option<Self> {
		Self::from_bits(input.read_byte()?)
	}
}
