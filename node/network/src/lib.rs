// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Substrate-specific network implementation.
//!
//! This manages gossip of consensus messages for BFT.

#![warn(unused_extern_crates)]

extern crate substrate_bft as bft;
#[macro_use]
extern crate substrate_network;
extern crate substrate_primitives;

extern crate node_consensus;
extern crate node_primitives;

extern crate futures;
extern crate tokio;
extern crate rhododendron;

#[macro_use]
extern crate log;

pub mod consensus;

use node_primitives::{Block, Hash};
use substrate_network::consensus_gossip::ConsensusGossip;

/// Specialization of the network service for the node protocol.
pub type NetworkService = ::substrate_network::Service<Block, Protocol, Hash>;

construct_simple_protocol! {
	/// Demo protocol attachment for substrate.
	pub struct Protocol where Block = Block {
		consensus_gossip: ConsensusGossip<Block>,
	}
}
