// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
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
