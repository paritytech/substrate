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

//! Generating request logic for request/response protocol for syncing BEEFY justifications.

use codec::Encode;
use futures::channel::{oneshot, oneshot::Canceled};
use log::{debug, warn};
use parking_lot::Mutex;
use sc_network::{
	request_responses::{IfDisconnected, RequestFailure},
	NetworkRequest, PeerId, ProtocolName,
};
use sp_consensus_beefy::{crypto::AuthorityId, ValidatorSet};
use sp_runtime::traits::{Block, NumberFor};
use std::{collections::VecDeque, result::Result, sync::Arc};

use crate::{
	communication::{
		benefit, cost,
		peers::PeerReport,
		request_response::{Error, JustificationRequest, BEEFY_SYNC_LOG_TARGET},
	},
	justification::{decode_and_verify_finality_proof, BeefyVersionedFinalityProof},
	metric_inc,
	metrics::{register_metrics, OnDemandOutgoingRequestsMetrics},
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

/// Possible engine responses.
pub(crate) enum ResponseInfo<B: Block> {
	/// No peer response available yet.
	Pending,
	/// Valid justification provided alongside peer reputation changes.
	ValidProof(BeefyVersionedFinalityProof<B>, PeerReport),
	/// No justification yet, only peer reputation changes.
	PeerReport(PeerReport),
}

pub struct OnDemandJustificationsEngine<B: Block> {
	network: Arc<dyn NetworkRequest + Send + Sync>,
	protocol_name: ProtocolName,

	live_peers: Arc<Mutex<KnownPeers<B>>>,
	peers_cache: VecDeque<PeerId>,

	state: State<B>,
	metrics: Option<OnDemandOutgoingRequestsMetrics>,
}

impl<B: Block> OnDemandJustificationsEngine<B> {
	pub fn new(
		network: Arc<dyn NetworkRequest + Send + Sync>,
		protocol_name: ProtocolName,
		live_peers: Arc<Mutex<KnownPeers<B>>>,
		prometheus_registry: Option<prometheus::Registry>,
	) -> Self {
		let metrics = register_metrics(prometheus_registry);
		Self {
			network,
			protocol_name,
			live_peers,
			peers_cache: VecDeque::new(),
			state: State::Idle,
			metrics,
		}
	}

	fn reset_peers_cache_for_block(&mut self, block: NumberFor<B>) {
		self.peers_cache = self.live_peers.lock().further_than(block);
	}

	fn try_next_peer(&mut self) -> Option<PeerId> {
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
			target: BEEFY_SYNC_LOG_TARGET,
			"🥩 requesting justif #{:?} from peer {:?}", req_info.block, peer,
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
			metric_inc!(self, beefy_on_demand_justification_no_peer_to_request_from);
			debug!(
				target: BEEFY_SYNC_LOG_TARGET,
				"🥩 no good peers to request justif #{:?} from", block
			);
		}
	}

	/// Cancel any pending request for block numbers smaller or equal to `block`.
	pub fn cancel_requests_older_than(&mut self, block: NumberFor<B>) {
		match &self.state {
			State::AwaitingResponse(_, req_info, _) if req_info.block <= block => {
				debug!(
					target: BEEFY_SYNC_LOG_TARGET,
					"🥩 cancel pending request for justification #{:?}", req_info.block
				);
				self.state = State::Idle;
			},
			_ => (),
		}
	}

	fn process_response(
		&mut self,
		peer: &PeerId,
		req_info: &RequestInfo<B>,
		response: Result<Response, Canceled>,
	) -> Result<BeefyVersionedFinalityProof<B>, Error> {
		response
			.map_err(|e| {
				debug!(
					target: BEEFY_SYNC_LOG_TARGET,
					"🥩 on-demand sc-network channel sender closed, err: {:?}", e
				);
				Error::ResponseError
			})?
			.map_err(|e| {
				debug!(
					target: BEEFY_SYNC_LOG_TARGET,
					"🥩 for on demand justification #{:?}, peer {:?} error: {:?}",
					req_info.block,
					peer,
					e
				);
				match e {
					RequestFailure::Refused => {
						metric_inc!(self, beefy_on_demand_justification_peer_refused);
						let peer_report =
							PeerReport { who: *peer, cost_benefit: cost::REFUSAL_RESPONSE };
						Error::InvalidResponse(peer_report)
					},
					_ => {
						metric_inc!(self, beefy_on_demand_justification_peer_error);
						Error::ResponseError
					},
				}
			})
			.and_then(|encoded| {
				decode_and_verify_finality_proof::<B>(
					&encoded[..],
					req_info.block,
					&req_info.active_set,
				)
				.map_err(|(err, signatures_checked)| {
					metric_inc!(self, beefy_on_demand_justification_invalid_proof);
					debug!(
						target: BEEFY_SYNC_LOG_TARGET,
						"🥩 for on demand justification #{:?}, peer {:?} responded with invalid proof: {:?}",
						req_info.block, peer, err
					);
					let mut cost = cost::INVALID_PROOF;
					cost.value +=
						cost::PER_SIGNATURE_CHECKED.saturating_mul(signatures_checked as i32);
					Error::InvalidResponse(PeerReport { who: *peer, cost_benefit: cost })
				})
			})
	}

	pub(crate) async fn next(&mut self) -> ResponseInfo<B> {
		let (peer, req_info, resp) = match &mut self.state {
			State::Idle => {
				futures::future::pending::<()>().await;
				return ResponseInfo::Pending
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
		match self.process_response(&peer, &req_info, resp) {
			Err(err) => {
				// No valid justification received, try next peer in our set.
				if let Some(peer) = self.try_next_peer() {
					self.request_from_peer(peer, req_info);
				} else {
					warn!(
						target: BEEFY_SYNC_LOG_TARGET,
						"🥩 ran out of peers to request justif #{:?} from", block
					);
				}
				// Report peer based on error type.
				if let Error::InvalidResponse(peer_report) = err {
					ResponseInfo::PeerReport(peer_report)
				} else {
					ResponseInfo::Pending
				}
			},
			Ok(proof) => {
				metric_inc!(self, beefy_on_demand_justification_good_proof);
				debug!(
					target: BEEFY_SYNC_LOG_TARGET,
					"🥩 received valid on-demand justif #{:?} from {:?}", block, peer
				);
				let peer_report = PeerReport { who: peer, cost_benefit: benefit::VALIDATED_PROOF };
				ResponseInfo::ValidProof(proof, peer_report)
			},
		}
	}
}
