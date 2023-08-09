// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
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

//! [`sync_with_runtime`] synchronises the session status and mixnode sets from the blockchain
//! runtime to the core mixnet state. It is called every time a block is finalised.

use super::peer_id::from_core_peer_id;
use libp2p_identity::PeerId;
use log::{error, warn};
use mixnet::core::{
	Mixnet, Mixnode as CoreMixnode, MixnodesErr as CoreMixnodesErr, RelSessionIndex,
	SessionPhase as CoreSessionPhase, SessionStatus as CoreSessionStatus,
};
use multiaddr::{multiaddr, Multiaddr, Protocol};
use sp_api::{ApiError, ApiRef};
use sp_mixnet::{
	runtime_api::MixnetApi,
	types::{
		Mixnode as RuntimeMixnode, MixnodesErr as RuntimeMixnodesErr,
		SessionPhase as RuntimeSessionPhase, SessionStatus as RuntimeSessionStatus,
	},
};
use sp_runtime::traits::Block;

const LOG_TARGET: &str = "mixnet";

/// Convert a [`RuntimeSessionStatus`] to a [`CoreSessionStatus`].
///
/// The [`RuntimeSessionStatus`] and [`CoreSessionStatus`] types are effectively the same.
/// [`RuntimeSessionStatus`] is used in the runtime to avoid depending on the [`mixnet`] crate
/// there.
fn to_core_session_status(status: RuntimeSessionStatus) -> CoreSessionStatus {
	CoreSessionStatus {
		current_index: status.current_index,
		phase: match status.phase {
			RuntimeSessionPhase::CoverToCurrent => CoreSessionPhase::CoverToCurrent,
			RuntimeSessionPhase::RequestsToCurrent => CoreSessionPhase::RequestsToCurrent,
			RuntimeSessionPhase::CoverToPrev => CoreSessionPhase::CoverToPrev,
			RuntimeSessionPhase::DisconnectFromPrev => CoreSessionPhase::DisconnectFromPrev,
		},
	}
}

/// Modify `external_addresses` such that there is at least one address and the final component of
/// each address matches `peer_id`.
fn fixup_external_addresses(external_addresses: &mut Vec<Multiaddr>, peer_id: &PeerId) {
	// Ensure the final component of each address matches peer_id
	external_addresses.retain_mut(|addr| match addr.iter().last() {
		Some(Protocol::P2p(addr_peer_id)) if addr_peer_id == *peer_id => true,
		Some(Protocol::P2p(_)) => {
			error!(
				target: LOG_TARGET,
				"Mixnode address {} does not match mixnode peer ID {}, ignoring",
				addr,
				peer_id
			);
			false
		},
		Some(_) | None => {
			addr.push(Protocol::P2p(*peer_id));
			true
		},
	});

	// If there are no addresses, insert one consisting of just the peer ID
	if external_addresses.is_empty() {
		external_addresses.push(multiaddr!(P2p(*peer_id)));
	}
}

/// Convert a [`RuntimeMixnode`] to a [`CoreMixnode`]. If the conversion fails, an error message is
/// logged, but a [`CoreMixnode`] is still returned.
///
/// It would be possible to handle conversion failure in a better way, but this would complicate
/// things for what should be a rare case. Note that even if the conversion here succeeds, there is
/// no guarantee that we will be able to connect to the mixnode or send packets to it. The most
/// common failure case is expected to be that a mixnode is simply unreachable over the network.
fn into_core_mixnode(mixnode: RuntimeMixnode) -> CoreMixnode {
	// Parse external addresses
	let mut external_addresses = mixnode
		.external_addresses
		.into_iter()
		.flat_map(|addr| {
			let addr = match String::from_utf8(addr) {
				Ok(addr) => addr,
				Err(err) => {
					error!(target: LOG_TARGET,
						"Mixnode external address {:x?} is not valid UTF-8",
						err.into_bytes());
					return None
				},
			};
			match addr.parse() {
				Ok(addr) => Some(addr),
				Err(err) => {
					error!(target: LOG_TARGET,
						"Could not parse mixnode address {addr}: {err}");
					None
				},
			}
		})
		.collect();

	// Fixup external addresses
	if let Some(peer_id) = from_core_peer_id(&mixnode.peer_id) {
		fixup_external_addresses(&mut external_addresses, &peer_id);
	} else {
		error!(target: LOG_TARGET,
			"Failed to convert mixnet peer ID {:x?} to libp2p peer ID",
			mixnode.peer_id);
	}

	CoreMixnode { kx_public: mixnode.kx_public, peer_id: mixnode.peer_id, external_addresses }
}

fn maybe_set_mixnodes(
	mixnet: &mut Mixnet,
	rel_session_index: RelSessionIndex,
	mixnodes: &dyn Fn() -> Result<Result<Vec<RuntimeMixnode>, RuntimeMixnodesErr>, ApiError>,
) {
	let current_session_index = mixnet.session_status().current_index;
	mixnet.maybe_set_mixnodes(rel_session_index, &mut || {
		// Note that RelSessionIndex::Prev + 0 would panic, but this closure will not get called in
		// that case so we are fine. Do not move this out of the closure!
		let session_index = rel_session_index + current_session_index;
		match mixnodes() {
			Ok(Ok(mixnodes)) => Ok(mixnodes.into_iter().map(into_core_mixnode).collect()),
			Ok(Err(err)) => {
				warn!(target: LOG_TARGET, "Session {session_index}: Mixnet disabled: {err}");
				Err(CoreMixnodesErr::Permanent) // Disable the session slot
			},
			Err(err) => {
				error!(
					target: LOG_TARGET,
					"Session {session_index}: Error getting mixnodes from runtime: {err}"
				);
				Err(CoreMixnodesErr::Transient) // Just leave the session slot empty; try again next block
			},
		}
	});
}

pub fn sync_with_runtime<B, A>(mixnet: &mut Mixnet, api: ApiRef<A>, hash: B::Hash)
where
	B: Block,
	A: MixnetApi<B>,
{
	let session_status = match api.session_status(hash) {
		Ok(session_status) => session_status,
		Err(err) => {
			error!(target: LOG_TARGET, "Error getting session status from runtime: {err}");
			return
		},
	};
	mixnet.set_session_status(to_core_session_status(session_status));

	maybe_set_mixnodes(mixnet, RelSessionIndex::Prev, &|| api.prev_mixnodes(hash));
	maybe_set_mixnodes(mixnet, RelSessionIndex::Current, &|| api.current_mixnodes(hash));
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn fixup_empty_external_addresses() {
		let peer_id = PeerId::random();
		let mut external_addresses = Vec::new();
		fixup_external_addresses(&mut external_addresses, &peer_id);
		assert_eq!(external_addresses, vec![multiaddr!(P2p(peer_id))]);
	}

	#[test]
	fn fixup_misc_external_addresses() {
		let peer_id = PeerId::random();
		let other_peer_id = PeerId::random();
		let mut external_addresses = vec![
			multiaddr!(Tcp(0u16), P2p(peer_id)),
			multiaddr!(Tcp(1u16), P2p(other_peer_id)),
			multiaddr!(Tcp(2u16)),
			Multiaddr::empty(),
		];
		fixup_external_addresses(&mut external_addresses, &peer_id);
		assert_eq!(
			external_addresses,
			vec![
				multiaddr!(Tcp(0u16), P2p(peer_id)),
				multiaddr!(Tcp(2u16), P2p(peer_id)),
				multiaddr!(P2p(peer_id)),
			]
		);
	}
}
