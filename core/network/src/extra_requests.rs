// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};
use log::{trace, debug};
use consensus::import_queue::ImportQueue;
use network_libp2p::{Severity, NodeIndex};
use runtime_primitives::Justification;
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use crate::message::{self, Message, generic::Message as GenericMessage};
use crate::protocol::Context;
use crate::sync::{PeerSync, PeerSyncState};

// Time to wait before trying to get the same extra data from the same peer.
const EXTRA_RETRY_WAIT: Duration = Duration::from_secs(10);

/// Pending extra data request for the given block (hash and number).
type ExtraRequest<B> = (<B as BlockT>::Hash, NumberFor<B>);

/// Extra requests processor.
trait ExtraRequestsEssence<B: BlockT> {
	type Response;

	/// Name of request type to display in logs.
	fn type_name(&self) -> &'static str;
	/// Prepare network message corresponding to the request.
	fn into_network_request(&self, request: ExtraRequest<B>, last_finalzied_hash: B::Hash) -> Message<B>;
	/// Accept response.
	fn accept_response(&self, request: ExtraRequest<B>, import_queue: &ImportQueue<B>, response: Self::Response) -> ExtraResponseKind;
	///
	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B>;
}

/// Manages all extra data requests required for sync.
pub(crate) struct ExtraRequestsAggregator<B: BlockT> {
	/// Manages justifications requests.
	justifications: ExtraRequests<B, JustificationsRequestsEssence>,
	/// Manages finality proof requests.
	finality_proofs: ExtraRequests<B, FinalityProofRequestsEssence>,
}

impl<B: BlockT> ExtraRequestsAggregator<B> {
	pub fn new() -> Self {
		ExtraRequestsAggregator {
			justifications: ExtraRequests::new(JustificationsRequestsEssence),
			finality_proofs: ExtraRequests::new(FinalityProofRequestsEssence),
		}
	}

	pub fn request_justification(&mut self, request: &ExtraRequest<B>, peers: &mut HashMap<NodeIndex, PeerSync<B>>, protocol: &mut Context<B>) {
		self.justifications.queue_request(request);
		self.justifications.dispatch(peers, protocol);
	}

	pub fn request_finality_proof(&mut self, request: &ExtraRequest<B>, peers: &mut HashMap<NodeIndex, PeerSync<B>>, protocol: &mut Context<B>) {
		self.finality_proofs.queue_request(request);
		self.finality_proofs.dispatch(peers, protocol);
	}

	pub fn on_justification(&mut self, who: NodeIndex, justification: Option<Justification>, protocol: &mut Context<B>, import_queue: &ImportQueue<B>) {
		self.justifications.on_response(who, justification, protocol, import_queue);
	}

	pub fn on_finality_proof(&mut self, who: NodeIndex, finality_proof: Option<Vec<u8>>, protocol: &mut Context<B>, import_queue: &ImportQueue<B>) {
		self.finality_proofs.on_response(who, finality_proof, protocol, import_queue);
	}

	pub fn dispatch(&mut self, peers: &mut HashMap<NodeIndex, PeerSync<B>>, protocol: &mut Context<B>) {
		self.justifications.dispatch(peers, protocol);
		self.finality_proofs.dispatch(peers, protocol);
	}

	pub fn collect_garbage(&mut self, best_finalized: NumberFor<B>) {
		self.justifications.collect_garbage(best_finalized);
		self.finality_proofs.collect_garbage(best_finalized);
	}

	pub fn peer_disconnected(&mut self, who: NodeIndex) {
		self.justifications.peer_disconnected(who);
		self.finality_proofs.peer_disconnected(who);
	}
}

/// Manages pending extra data requests of single type.
struct ExtraRequests<B: BlockT, Essence> {
	requests: HashSet<ExtraRequest<B>>,
	pending_requests: VecDeque<ExtraRequest<B>>,
	peer_requests: HashMap<NodeIndex, ExtraRequest<B>>,
	previous_requests: HashMap<ExtraRequest<B>, Vec<(NodeIndex, Instant)>>,
	essence: Essence,
}

impl<B: BlockT, Essence: ExtraRequestsEssence<B>> ExtraRequests<B, Essence> {
	fn new(essence: Essence) -> Self {
		ExtraRequests {
			requests: HashSet::new(),
			pending_requests: VecDeque::new(),
			peer_requests: HashMap::new(),
			previous_requests: HashMap::new(),
			essence,
		}
	}

	/// Dispatches all possible pending requests to the given peers. Peers are
	/// filtered according to the current known best block (i.e. we won't send a
	/// extra request for block #10 to a peer at block #2), and we also
	/// throttle requests to the same peer if a previous extra request
	/// yielded no results.
	fn dispatch(&mut self, peers: &mut HashMap<NodeIndex, PeerSync<B>>, protocol: &mut Context<B>) {
		if self.pending_requests.is_empty() {
			return;
		}

		let initial_pending_requests = self.pending_requests.len();

		// clean up previous failed requests so we can retry again
		for (_, requests) in self.previous_requests.iter_mut() {
			requests.retain(|(_, instant)| instant.elapsed() < EXTRA_RETRY_WAIT);
		}

		let mut available_peers = peers.iter().filter_map(|(peer, sync)| {
			// don't request to any peers that already have pending requests or are unavailable
			if sync.state != PeerSyncState::Available || self.peer_requests.contains_key(&peer) {
				None
			} else {
				Some((*peer, sync.best_number))
			}
		}).collect::<VecDeque<_>>();

		let mut last_peer = available_peers.back().map(|p| p.0);
		let mut unhandled_requests = VecDeque::new();

		let last_finalzied_hash = match protocol.client().info() {
			Ok(info) => info.chain.finalized_hash,
			Err(e) => {
				debug!(target:"sync", "Cannot dispatch {} requests: error {:?} when reading blockchain", self.essence.type_name(), e);
				return;
			},
		};

		loop {
			let (peer, peer_best_number) = match available_peers.pop_front() {
				Some(p) => p,
				_ => break,
			};

			// only ask peers that have synced past the block number that we're
			// asking the extra data for and to whom we haven't already made
			// the same request recently
			let peer_eligible = {
				let request = match self.pending_requests.front() {
					Some(r) => r.clone(),
					_ => break,
				};

				peer_best_number >= request.1 &&
					!self.previous_requests
						 .get(&request)
						 .map(|requests| requests.iter().any(|i| i.0 == peer))
						 .unwrap_or(false)
			};

			if !peer_eligible {
				available_peers.push_back((peer, peer_best_number));

				// we tried all peers and none can answer this request
				if Some(peer) == last_peer {
					last_peer = available_peers.back().map(|p| p.0);

					let request = self.pending_requests.pop_front()
						.expect("verified to be Some in the beginning of the loop; qed");

					unhandled_requests.push_back(request);
				}

				continue;
			}

			last_peer = available_peers.back().map(|p| p.0);

			let request = self.pending_requests.pop_front()
				.expect("verified to be Some in the beginning of the loop; qed");

			self.peer_requests.insert(peer, request);

			peers.get_mut(&peer)
				.expect("peer was is taken from available_peers; available_peers is a subset of peers; qed")
				.state = self.essence.peer_downloading_state(request.0);

			trace!(target: "sync", "Requesting {} for block #{} from {}", self.essence.type_name(), request.0, peer);
			let request = self.essence.into_network_request(request, last_finalzied_hash);

			protocol.send_message(peer, request);
		}

		self.pending_requests.append(&mut unhandled_requests);

		trace!(target: "sync", "Dispatched {} {} requests ({} pending)",
			initial_pending_requests - self.pending_requests.len(),
			self.essence.type_name(),
			self.pending_requests.len(),
		);
	}

	/// Queue a justification request (without dispatching it).
	fn queue_request(&mut self, request: &ExtraRequest<B>) {
		if !self.requests.insert(*request) {
			return;
		}
		self.pending_requests.push_back(*request);
	}

	/// Retry any pending request if a peer disconnected.
	fn peer_disconnected(&mut self, who: NodeIndex) {
		if let Some(request) = self.peer_requests.remove(&who) {
			self.pending_requests.push_front(request);
		}
	}

	/// Processes the response for the request previously sent to the given
	/// peer. Queues a retry in case the import fails or the given justification
	/// was `None`.
	fn on_response(
		&mut self,
		who: NodeIndex,
		response: Essence::Response,
		protocol: &mut Context<B>,
		import_queue: &ImportQueue<B>,
	) {
		// we assume that the request maps to the given response, this is
		// currently enforced by the outer network protocol before passing on
		// messages to chain sync.
		if let Some(request) = self.peer_requests.remove(&who) {
			match self.essence.accept_response(request, import_queue, response) {
				ExtraResponseKind::Accepted => {
					trace!(target: "sync", "Accepted {} response for {} from {}.", self.essence.type_name(), request.0, who);
					self.requests.remove(&request);
					self.previous_requests.remove(&request);
					return;
				},
				ExtraResponseKind::Invalid => {
					trace!(target: "sync", "Invalid {} provided for {} by {}", self.essence.type_name(), request.0, who);
					protocol.report_peer(
						who,
						Severity::Bad(format!("Invalid {} provided for {} by {}", self.essence.type_name(), request.0, who)),
					);
				},
				ExtraResponseKind::Missing => {
					trace!(target: "sync", "Empty {} response for {} has provided by {}", self.essence.type_name(), request.0, who);
					self.previous_requests
						.entry(request)
						.or_insert(Vec::new())
						.push((who, Instant::now()));
				},
			}

			self.pending_requests.push_front(request);
		} else {
			trace!(target: "sync", "Ignoring {} response from {}. No pending request.", self.essence.type_name(), who);
		}
	}

	/// Removes any pending justification requests for blocks lower than the
	/// given best finalized.
	fn collect_garbage(&mut self, best_finalized: NumberFor<B>) {
		self.requests.retain(|(_, n)| *n > best_finalized);
		self.pending_requests.retain(|(_, n)| *n > best_finalized);
		self.peer_requests.retain(|_, (_, n)| *n > best_finalized);
		self.previous_requests.retain(|(_, n), _| *n > best_finalized);
	}
}

enum ExtraResponseKind {
	Accepted,
	Invalid,
	Missing,
}

struct JustificationsRequestsEssence;

impl<B: BlockT> ExtraRequestsEssence<B> for JustificationsRequestsEssence {
	type Response = Option<Justification>;

	fn type_name(&self) -> &'static str {
		"justification"
	}

	fn into_network_request(&self, request: ExtraRequest<B>, _last_finalzied_hash: B::Hash) -> Message<B> {
		GenericMessage::BlockRequest(message::generic::BlockRequest {
			id: 0,
			fields: message::BlockAttributes::JUSTIFICATION,
			from: message::FromBlock::Hash(request.0),
			to: None,
			direction: message::Direction::Ascending,
			max: Some(1),
		})
	}

	fn accept_response(&self, request: ExtraRequest<B>, import_queue: &ImportQueue<B>, response: Option<Justification>) -> ExtraResponseKind {
		if let Some(justification) = response {
			if import_queue.import_justification(request.0, request.1, justification) {
				ExtraResponseKind::Accepted
			} else {
				ExtraResponseKind::Invalid
			}
		} else {
			ExtraResponseKind::Missing
		}
	}

	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B> {
		PeerSyncState::DownloadingJustification(block)
	}
}

struct FinalityProofRequestsEssence;

impl<B: BlockT> ExtraRequestsEssence<B> for FinalityProofRequestsEssence {
	type Response = Option<Vec<u8>>;

	fn type_name(&self) -> &'static str {
		"finality proof"
	}

	fn into_network_request(&self, request: ExtraRequest<B>, last_finalzied_hash: B::Hash) -> Message<B> {
		GenericMessage::FinalityProofRequest(message::generic::FinalityProofRequest {
			block: request.0,
			last_finalized: last_finalzied_hash,
		})
	}

	fn accept_response(&self, request: ExtraRequest<B>, import_queue: &ImportQueue<B>, response: Option<Vec<u8>>) -> ExtraResponseKind {
		if let Some(finality_proof) = response {
			if import_queue.import_finality_proof(request.0, request.1, finality_proof) {
				ExtraResponseKind::Accepted
			} else {
				ExtraResponseKind::Invalid
			}
		} else {
			ExtraResponseKind::Missing
		}
	}

	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B> {
		PeerSyncState::DownloadingFinalityProof(block)
	}
}