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

//! Generating request logic for request/response protocol for syncing BEEFY justifications.

use beefy_primitives::{crypto::AuthorityId, ValidatorSet};
use codec::Encode;
use futures::channel::{oneshot, oneshot::Canceled};
use log::{debug, warn};
use parking_lot::Mutex;
use sc_network::{PeerId, ProtocolName};
use sc_network_common::{
	request_responses::{IfDisconnected, RequestFailure},
	service::NetworkRequest,
};
use sp_runtime::traits::{Block, NumberFor};
use std::{collections::VecDeque, result::Result, sync::Arc};

use crate::{
	communication::request_response::{Error, JustificationRequest},
	justification::{decode_and_verify_finality_proof, BeefyVersionedFinalityProof},
	KnownPeers,
};

/// Response type received from network.
type Response = Result<Vec<u8>, RequestFailure>;
/// Used to receive a response from the network.
type ResponseReceiver = oneshot::Receiver<Response>;

#[derive(Clone, Debug)]
struct RequestInfo<B: Block> {
	block: NumberFor<B>,
	active_set: ValidatorSet<AuthorityId>,
}

enum State<B: Block> {
	Idle,
	AwaitingResponse(PeerId, RequestInfo<B>, ResponseReceiver),
}

pub struct OnDemandJustificationsEngine<B: Block> {
	network: Arc<dyn NetworkRequest + Send + Sync>,
	protocol_name: ProtocolName,

	live_peers: Arc<Mutex<KnownPeers<B>>>,
	peers_cache: VecDeque<PeerId>,

	state: State<B>,
}

impl<B: Block> OnDemandJustificationsEngine<B> {
	pub fn new(
		network: Arc<dyn NetworkRequest + Send + Sync>,
		protocol_name: ProtocolName,
		live_peers: Arc<Mutex<KnownPeers<B>>>,
	) -> Self {
		Self {
			network,
			protocol_name,
			live_peers,
			peers_cache: VecDeque::new(),
			state: State::Idle,
		}
	}

	fn reset_peers_cache_for_block(&mut self, block: NumberFor<B>) {
		// TODO (issue #12296): replace peer selection with generic one that involves all protocols.
		self.peers_cache = self.live_peers.lock().at_least_at_block(block);
	}

	fn try_next_peer(&mut self) -> Option<PeerId> {
		// TODO (issue #12296): replace peer selection with generic one that involves all protocols.
		let live = self.live_peers.lock();
		while let Some(peer) = self.peers_cache.pop_front() {
			if live.contains(&peer) {
				return Some(peer)
			}
		}
		None
	}

	fn request_from_peer(&mut self, peer: PeerId, req_info: RequestInfo<B>) {
		debug!(
			target: "beefy::sync",
			"🥩 requesting justif #{:?} from peer {:?}",
			req_info.block,
			peer,
		);

		let payload = JustificationRequest::<B> { begin: req_info.block }.encode();

		let (tx, rx) = oneshot::channel();

		self.network.start_request(
			peer,
			self.protocol_name.clone(),
			payload,
			tx,
			IfDisconnected::ImmediateError,
		);

		self.state = State::AwaitingResponse(peer, req_info, rx);
	}

	/// Start new justification request for `block`, if no other request is in progress.
	///
	/// `active_set` will be used to verify validity of potential responses.
	pub fn request(&mut self, block: NumberFor<B>, active_set: ValidatorSet<AuthorityId>) {
		// ignore new requests while there's already one pending
		if matches!(self.state, State::AwaitingResponse(_, _, _)) {
			return
		}
		self.reset_peers_cache_for_block(block);

		// Start the requests engine - each unsuccessful received response will automatically
		// trigger a new request to the next peer in the `peers_cache` until there are none left.
		if let Some(peer) = self.try_next_peer() {
			self.request_from_peer(peer, RequestInfo { block, active_set });
		} else {
			debug!(target: "beefy::sync", "🥩 no good peers to request justif #{:?} from", block);
		}
	}

	/// Cancel any pending request for block numbers smaller or equal to `block`.
	pub fn cancel_requests_older_than(&mut self, block: NumberFor<B>) {
		match &self.state {
			State::AwaitingResponse(_, req_info, _) if req_info.block <= block => {
				debug!(
					target: "beefy::sync", "🥩 cancel pending request for justification #{:?}",
					req_info.block
				);
				self.state = State::Idle;
			},
			_ => (),
		}
	}

	fn process_response(
		&mut self,
		peer: PeerId,
		req_info: &RequestInfo<B>,
		response: Result<Response, Canceled>,
	) -> Result<BeefyVersionedFinalityProof<B>, Error> {
		response
			.map_err(|e| {
				debug!(
					target: "beefy::sync",
					"🥩 for on demand justification #{:?}, peer {:?} hung up: {:?}",
					req_info.block, peer, e
				);
				Error::InvalidResponse
			})?
			.map_err(|e| {
				debug!(
					target: "beefy::sync",
					"🥩 for on demand justification #{:?}, peer {:?} error: {:?}",
					req_info.block, peer, e
				);
				Error::InvalidResponse
			})
			.and_then(|encoded| {
				decode_and_verify_finality_proof::<B>(
					&encoded[..],
					req_info.block,
					&req_info.active_set,
				)
				.map_err(|e| {
					debug!(
						target: "beefy::sync",
						"🥩 for on demand justification #{:?}, peer {:?} responded with invalid proof: {:?}",
						req_info.block, peer, e
					);
					Error::InvalidResponse
				})
			})
	}

	pub async fn next(&mut self) -> Option<BeefyVersionedFinalityProof<B>> {
		let (peer, req_info, resp) = match &mut self.state {
			State::Idle => {
				futures::pending!();
				// Doesn't happen as 'futures::pending!()' is an 'await' barrier that never passes.
				return None
			},
			State::AwaitingResponse(peer, req_info, receiver) => {
				let resp = receiver.await;
				(*peer, req_info.clone(), resp)
			},
		};
		// We received the awaited response. Our 'receiver' will never generate any other response,
		// meaning we're done with current state. Move the engine to `State::Idle`.
		self.state = State::Idle;

		let block = req_info.block;
		self.process_response(peer, &req_info, resp)
			.map_err(|_| {
				// No valid justification received, try next peer in our set.
				if let Some(peer) = self.try_next_peer() {
					self.request_from_peer(peer, req_info);
				} else {
					warn!(target: "beefy::sync", "🥩 ran out of peers to request justif #{:?} from", block);
				}
			})
			.map(|proof| {
				debug!(
					target: "beefy::sync",
					"🥩 received valid on-demand justif #{:?} from {:?}",
					block, peer
				);
				proof
			})
			.ok()
	}
}
