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

use beefy_primitives::{crypto::AuthorityId, BeefyApi, ValidatorSet};
use codec::Encode;
use futures::{
	channel::{oneshot, oneshot::Canceled},
	stream::{self, StreamExt},
};
use log::{debug, error, warn};
use parking_lot::Mutex;
use sc_network::{PeerId, ProtocolName};
use sc_network_common::{
	request_responses::{IfDisconnected, RequestFailure},
	service::NetworkRequest,
};
use sp_api::ProvideRuntimeApi;
use sp_runtime::{
	generic::BlockId,
	traits::{Block, NumberFor},
};
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

enum State<B: Block> {
	Idle(stream::Pending<Result<Response, Canceled>>),
	AwaitingResponse(PeerId, NumberFor<B>, stream::Once<ResponseReceiver>),
}

pub struct OnDemandJustificationsEngine<B: Block, R> {
	network: Arc<dyn NetworkRequest + Send + Sync>,
	runtime: Arc<R>,
	protocol_name: ProtocolName,

	live_peers: Arc<Mutex<KnownPeers<B>>>,
	peers_cache: VecDeque<PeerId>,

	state: State<B>,
}

impl<B, R> OnDemandJustificationsEngine<B, R>
where
	B: Block,
	R: ProvideRuntimeApi<B>,
	R::Api: BeefyApi<B>,
{
	pub fn new(
		network: Arc<dyn NetworkRequest + Send + Sync>,
		runtime: Arc<R>,
		protocol_name: ProtocolName,
		live_peers: Arc<Mutex<KnownPeers<B>>>,
	) -> Self {
		Self {
			network,
			runtime,
			protocol_name,
			live_peers,
			peers_cache: VecDeque::new(),
			state: State::Idle(stream::pending()),
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

	fn request_from_peer(&mut self, peer: PeerId, block: NumberFor<B>) {
		debug!(target: "beefy::sync", "🥩 requesting justif #{:?} from peer {:?}", block, peer);

		let payload = JustificationRequest::<B> { begin: block }.encode();

		let (tx, rx) = oneshot::channel();

		self.network.start_request(
			peer,
			self.protocol_name.clone(),
			payload,
			tx,
			IfDisconnected::ImmediateError,
		);

		self.state = State::AwaitingResponse(peer, block, stream::once(rx));
	}

	/// If no other request is in progress, start new justification request for `block`.
	pub fn request(&mut self, block: NumberFor<B>) {
		// ignore new requests while there's already one pending
		match &self.state {
			State::AwaitingResponse(_, _, _) => return,
			State::Idle(_) => (),
		}
		self.reset_peers_cache_for_block(block);

		// Start the requests engine - each unsuccessful received response will automatically
		// trigger a new request to the next peer in the `peers_cache` until there are none left.
		if let Some(peer) = self.try_next_peer() {
			self.request_from_peer(peer, block);
		} else {
			debug!(target: "beefy::sync", "🥩 no good peers to request justif #{:?} from", block);
		}
	}

	/// Cancel any pending request for block numbers smaller or equal to `block`.
	pub fn cancel_requests_older_than(&mut self, block: NumberFor<B>) {
		match &self.state {
			State::AwaitingResponse(_, number, _) if *number <= block => {
				debug!(
					target: "beefy::sync",
					"🥩 cancel pending request for justification #{:?}",
					number
				);
				self.state = State::Idle(stream::pending());
			},
			_ => (),
		}
	}

	fn process_response(
		&mut self,
		peer: PeerId,
		block: NumberFor<B>,
		validator_set: &ValidatorSet<AuthorityId>,
		response: Result<Response, Canceled>,
	) -> Result<BeefyVersionedFinalityProof<B>, Error> {
		response
			.map_err(|e| {
				debug!(
					target: "beefy::sync",
					"🥩 for on demand justification #{:?}, peer {:?} hung up: {:?}",
					block, peer, e
				);
				Error::InvalidResponse
			})?
			.map_err(|e| {
				debug!(
					target: "beefy::sync",
					"🥩 for on demand justification #{:?}, peer {:?} error: {:?}",
					block, peer, e
				);
				Error::InvalidResponse
			})
			.and_then(|encoded| {
				decode_and_verify_finality_proof::<B>(&encoded[..], block, &validator_set).map_err(
					|e| {
						debug!(
							target: "beefy::sync",
							"🥩 for on demand justification #{:?}, peer {:?} responded with invalid proof: {:?}",
							block, peer, e
						);
						Error::InvalidResponse
					},
				)
			})
	}

	pub async fn next(&mut self) -> Option<BeefyVersionedFinalityProof<B>> {
		let (peer, block, resp) = match &mut self.state {
			State::Idle(pending) => {
				let _ = pending.next().await;
				// This never happens since 'stream::pending' never generates any items.
				return None
			},
			State::AwaitingResponse(peer, block, receiver) => {
				let resp = receiver.next().await?;
				(*peer, *block, resp)
			},
		};
		// We received the awaited response. Our 'stream::once()' receiver will never generate any
		// other response, meaning we're done with current state. Move the engine to `State::Idle`.
		self.state = State::Idle(stream::pending());

		let block_id = BlockId::number(block);
		let validator_set = self
			.runtime
			.runtime_api()
			.validator_set(&block_id)
			.map_err(|e| {
				error!(target: "beefy::sync", "🥩 Runtime API error {:?} in on-demand justif engine.", e);
				e
			})
			.ok()?
			.or_else(|| {
				error!(target: "beefy::sync", "🥩 BEEFY pallet not available for block {:?}.", block);
				None
			})?;

		self.process_response(peer, block, &validator_set, resp)
			.map_err(|_| {
				// No valid justification received, try next peer in our set.
				if let Some(peer) = self.try_next_peer() {
					self.request_from_peer(peer, block);
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
