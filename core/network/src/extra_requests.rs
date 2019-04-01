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
use log::{trace, warn, debug};
use client::error::Error as ClientError;
use consensus::import_queue::{ImportQueue, SharedFinalityProofRequestBuilder};
use fork_tree::ForkTree;
use network_libp2p::PeerId;
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
pub(crate) trait ExtraRequestsEssence<B: BlockT> {
	type Response;

	/// Name of request type to display in logs.
	fn type_name(&self) -> &'static str;
	/// Prepare network message corresponding to the request.
	fn into_network_request(&self, request: ExtraRequest<B>) -> Message<B>;
	/// Accept response.
	fn import_response(
		&self,
		import_queue: &ImportQueue<B>,
		who: PeerId,
		request: ExtraRequest<B>,
		response: Self::Response,
	);
	/// Create peer state for peer that is downloading extra data.
	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B>;
}

/// Manages all extra data requests required for sync.
pub(crate) struct ExtraRequestsAggregator<B: BlockT> {
	/// Manages justifications requests.
	justifications: ExtraRequests<B, JustificationsRequestsEssence>,
	/// Manages finality proof requests.
	finality_proofs: ExtraRequests<B, FinalityProofRequestsEssence<B>>,
}

impl<B: BlockT> ExtraRequestsAggregator<B> {
	pub(crate) fn new() -> Self {
		ExtraRequestsAggregator {
			justifications: ExtraRequests::new(JustificationsRequestsEssence),
			finality_proofs: ExtraRequests::new(FinalityProofRequestsEssence(None)),
		}
	}

	pub(crate) fn justifications(&mut self) -> &mut ExtraRequests<B, JustificationsRequestsEssence> {
		&mut self.justifications
	}

	pub(crate) fn finality_proofs(&mut self) -> &mut ExtraRequests<B, FinalityProofRequestsEssence<B>> {
		&mut self.finality_proofs
	}

	/// Dispatches all possible pending requests to the given peers.
	pub(crate) fn dispatch(&mut self, peers: &mut HashMap<PeerId, PeerSync<B>>, protocol: &mut Context<B>) {
		self.justifications.dispatch(peers, protocol);
		self.finality_proofs.dispatch(peers, protocol);
	}

	/// Removes any pending extra requests for blocks lower than the
	/// given best finalized.
	pub(crate) fn on_block_finalized<F>(
		&mut self,
		best_finalized_hash: &B::Hash,
		best_finalized_number: NumberFor<B>,
		is_descendent_of: &F,
	) -> Result<(), fork_tree::Error<ClientError>>
		where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError>
	{
		self.justifications.on_block_finalized(best_finalized_hash, best_finalized_number, is_descendent_of)?;
		self.finality_proofs.on_block_finalized(best_finalized_hash, best_finalized_number, is_descendent_of)?;
		Ok(())
	}

	/// Retry any pending request if a peer disconnected.
	pub(crate) fn peer_disconnected(&mut self, who: PeerId) {
		self.justifications.peer_disconnected(&who);
		self.finality_proofs.peer_disconnected(&who);
	}

	/// Clear all data.
	pub(crate) fn clear(&mut self) {
		self.justifications.clear();
		self.finality_proofs.clear();
	}
}

/// Manages pending block extra data (e.g. justification) requests.
/// Multiple extras may be requested for competing forks, or for the same branch
/// at different (increasing) heights. This structure will guarantee that extras
/// are fetched in-order, and that obsolete changes are pruned (when finalizing a
/// competing fork).
pub(crate) struct ExtraRequests<B: BlockT, Essence> {
	tree: ForkTree<B::Hash, NumberFor<B>, ()>,
	pending_requests: VecDeque<ExtraRequest<B>>,
	peer_requests: HashMap<PeerId, ExtraRequest<B>>,
	previous_requests: HashMap<ExtraRequest<B>, Vec<(PeerId, Instant)>>,
	importing_requests: HashSet<ExtraRequest<B>>,
	essence: Essence,
}

impl<B: BlockT, Essence: ExtraRequestsEssence<B>> ExtraRequests<B, Essence> {
	fn new(essence: Essence) -> Self {
		ExtraRequests {
			tree: ForkTree::new(),
			pending_requests: VecDeque::new(),
			peer_requests: HashMap::new(),
			previous_requests: HashMap::new(),
			importing_requests: HashSet::new(),
			essence,
		}
	}

	/// Get mutable reference to the requests essence.
	pub(crate) fn essence(&mut self) -> &mut Essence {
		&mut self.essence
	}

	/// Dispatches all possible pending requests to the given peers. Peers are
	/// filtered according to the current known best block (i.e. we won't send a
	/// extra request for block #10 to a peer at block #2), and we also
	/// throttle requests to the same peer if a previous justification request
	/// yielded no results.
	pub(crate) fn dispatch(&mut self, peers: &mut HashMap<PeerId, PeerSync<B>>, protocol: &mut Context<B>) {
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
				Some((peer.clone(), sync.best_number))
			}
		}).collect::<VecDeque<_>>();

		let mut last_peer = available_peers.back().map(|p| p.0.clone());
		let mut unhandled_requests = VecDeque::new();

		loop {
			let (peer, peer_best_number) = match available_peers.pop_front() {
				Some(p) => p,
				_ => break,
			};

			// only ask peers that have synced past the block number that we're
			// asking the extra for and to whom we haven't already made
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
				available_peers.push_back((peer.clone(), peer_best_number));

				// we tried all peers and none can answer this request
				if Some(peer) == last_peer {
					last_peer = available_peers.back().map(|p| p.0.clone());

					let request = self.pending_requests.pop_front()
						.expect("verified to be Some in the beginning of the loop; qed");

					unhandled_requests.push_back(request);
				}

				continue;
			}

			last_peer = available_peers.back().map(|p| p.0.clone());

			let request = self.pending_requests.pop_front()
				.expect("verified to be Some in the beginning of the loop; qed");

			self.peer_requests.insert(peer.clone(), request);

			peers.get_mut(&peer)
				.expect("peer was is taken from available_peers; available_peers is a subset of peers; qed")
				.state = self.essence.peer_downloading_state(request.0.clone());

			trace!(target: "sync", "Requesting {} for block #{} from {}", self.essence.type_name(), request.0, peer);
			let request = self.essence.into_network_request(request);

			protocol.send_message(peer, request);
		}

		self.pending_requests.append(&mut unhandled_requests);

		trace!(target: "sync", "Dispatched {} {} requests ({} pending)",
			initial_pending_requests - self.pending_requests.len(),
			self.essence.type_name(),
			self.pending_requests.len(),
		);
	}

	/// Queue a extra data request (without dispatching it).
	pub(crate) fn queue_request<F>(&mut self, request: ExtraRequest<B>, is_descendent_of: F)
		where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError>
	{
		match self.tree.import(request.0.clone(), request.1.clone(), (), &is_descendent_of) {
			Ok(true) => {
				// this is a new root so we add it to the current `pending_requests`
				self.pending_requests.push_back((request.0, request.1));
			},
			Err(err) => {
				warn!(target: "sync", "Failed to insert requested {} {:?} {:?} into tree: {:?}",
					self.essence.type_name(),
					request.0,
					request.1,
					err,
				);
				return;
			},
			_ => {},
		}
	}

	/// Retry any pending request if a peer disconnected.
	fn peer_disconnected(&mut self, who: &PeerId) {
		if let Some(request) = self.peer_requests.remove(who) {
			self.pending_requests.push_front(request);
		}
	}

	/// Process the import result of an extra.
	/// Queues a retry in case the import failed.
	pub(crate) fn on_import_result(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		let request = (hash, number);

		if !self.importing_requests.remove(&request) {
			debug!(target: "sync", "Got {} import result for unknown {} {:?} {:?} request.",
				self.essence.type_name(),
				self.essence.type_name(),
				request.0,
				request.1,
			);

 			return;
		}

		if success {
			if self.tree.finalize_root(&request.0).is_none() {
				warn!(target: "sync", "Imported {} for {:?} {:?} which isn't a root in the tree: {:?}",
					self.essence.type_name(),
					request.0,
					request.1,
					self.tree.roots().collect::<Vec<_>>(),
				);
				return;
			};

			self.previous_requests.clear();
			self.peer_requests.clear();
			self.pending_requests =
				self.tree.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect();

			return;
		}
		self.pending_requests.push_front(request);
	}

	/// Processes the response for the request previously sent to the given
	/// peer. Queues a retry in case the given justification
	/// was `None`.
	pub(crate) fn on_response(
		&mut self,
		who: PeerId,
		response: Option<Essence::Response>,
		import_queue: &ImportQueue<B>,
	) {
		// we assume that the request maps to the given response, this is
		// currently enforced by the outer network protocol before passing on
		// messages to chain sync.
		if let Some(request) = self.peer_requests.remove(&who) {
			if let Some(response) = response {
				self.essence.import_response(import_queue, who.clone(), request, response);
				self.importing_requests.insert(request);
				return;
			}

			self.previous_requests
				.entry(request)
				.or_insert(Vec::new())
				.push((who, Instant::now()));
			self.pending_requests.push_front(request);
		}
	}

	/// Removes any pending extra requests for blocks lower than the
	/// given best finalized.
	fn on_block_finalized<F>(
		&mut self,
		best_finalized_hash: &B::Hash,
		best_finalized_number: NumberFor<B>,
		is_descendent_of: F,
	) -> Result<(), fork_tree::Error<ClientError>>
		where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError>
	{
		if self.importing_requests.contains(&(*best_finalized_hash, best_finalized_number)) {
			// we imported this extra data ourselves, so we should get back a response
			// from the import queue through `on_import_result`
			return Ok(());
		}

		use std::collections::HashSet;

		self.tree.finalize(best_finalized_hash, best_finalized_number, &is_descendent_of)?;

		let roots = self.tree.roots().collect::<HashSet<_>>();

		self.pending_requests.retain(|(h, n)| roots.contains(&(h, n, &())));
		self.peer_requests.retain(|_, (h, n)| roots.contains(&(h, n, &())));
		self.previous_requests.retain(|(h, n), _| roots.contains(&(h, n, &())));

		Ok(())
	}

	/// Clear all data.
	pub(crate) fn clear(&mut self) {
		self.tree = ForkTree::new();
		self.pending_requests.clear();
		self.peer_requests.clear();
		self.previous_requests.clear();
	}
}

pub(crate) struct JustificationsRequestsEssence;

impl<B: BlockT> ExtraRequestsEssence<B> for JustificationsRequestsEssence {
	type Response = Justification;

	fn type_name(&self) -> &'static str {
		"justification"
	}

	fn into_network_request(&self, request: ExtraRequest<B>) -> Message<B> {
		GenericMessage::BlockRequest(message::generic::BlockRequest {
			id: 0,
			fields: message::BlockAttributes::JUSTIFICATION,
			from: message::FromBlock::Hash(request.0),
			to: None,
			direction: message::Direction::Ascending,
			max: Some(1),
		})
	}

	fn import_response(&self, import_queue: &ImportQueue<B>, who: PeerId, request: ExtraRequest<B>, response: Self::Response) {
		import_queue.import_justification(who, request.0, request.1, response)
	}

	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B> {
		PeerSyncState::DownloadingJustification(block)
	}
}

pub(crate) struct FinalityProofRequestsEssence<B: BlockT>(pub Option<SharedFinalityProofRequestBuilder<B>>);

impl<B: BlockT> ExtraRequestsEssence<B> for FinalityProofRequestsEssence<B> {
	type Response = Vec<u8>;

	fn type_name(&self) -> &'static str {
		"finality proof"
	}

	fn into_network_request(&self, request: ExtraRequest<B>) -> Message<B> {
		GenericMessage::FinalityProofRequest(message::generic::FinalityProofRequest {
			id: 0,
			block: request.0,
			request: self.0.as_ref()
				.map(|builder| builder.build_request_data(&request.0))
				.unwrap_or_default(),
		})
	}

	fn import_response(&self, import_queue: &ImportQueue<B>, who: PeerId, request: ExtraRequest<B>, response: Self::Response) {
		import_queue.import_finality_proof(who, request.0, request.1, response)
	}

	fn peer_downloading_state(&self, block: B::Hash) -> PeerSyncState<B> {
		PeerSyncState::DownloadingFinalityProof(block)
	}
}