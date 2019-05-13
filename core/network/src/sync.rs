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

//! Contains the state of the chain synchronization process
//!
//! At any given point in time, a running node tries as much as possible to be at the head of the
//! chain. This module handles the logic of which blocks to request from remotes, and processing
//! responses. It yields blocks to check and potentially move to the database.
//!
//! # Usage
//!
//! The `ChainSync` struct maintains the state of the block requests. Whenever something happens on
//! the network, or whenever a block has been successfully verified, call the appropriate method in
//! order to update it. You must also regularly call `tick()`.
//!
//! To each of these methods, you must pass a `Context` object that the `ChainSync` will use to
//! send its new outgoing requests.
//!

use std::cmp::max;
use std::collections::{HashMap, VecDeque};
use std::time::{Duration, Instant};
use log::{debug, trace, info, warn};
use crate::protocol::Context;
use fork_tree::ForkTree;
use network_libp2p::PeerId;
use client::{BlockStatus, ClientInfo};
use consensus::{BlockOrigin, import_queue::IncomingBlock};
use client::error::Error as ClientError;
use crate::blocks::BlockCollection;
use runtime_primitives::Justification;
use runtime_primitives::traits::{Block as BlockT, Header as HeaderT, As, NumberFor, Zero, CheckedSub};
use runtime_primitives::generic::BlockId;
use crate::message;
use crate::config::Roles;
use std::collections::HashSet;

// Maximum blocks to request in a single packet.
const MAX_BLOCKS_TO_REQUEST: usize = 128;
// Maximum blocks to store in the import queue.
const MAX_IMPORTING_BLOCKS: usize = 2048;
// Number of blocks in the queue that prevents ancestry search.
const MAJOR_SYNC_BLOCKS: usize = 5;
// Time to wait before trying to get a justification from the same peer.
const JUSTIFICATION_RETRY_WAIT: Duration = Duration::from_secs(10);
// Number of recently announced blocks to track for each peer.
const ANNOUNCE_HISTORY_SIZE: usize = 64;
// Max number of blocks to download for unknown forks.
const MAX_UNKNOWN_FORK_DOWNLOAD_LEN: u32 = 32;
/// Reputation change when a peer sent us a status message that led to a database read error.
const BLOCKCHAIN_STATUS_READ_ERROR_REPUTATION_CHANGE: i32 = -(1 << 16);
/// Reputation change when a peer failed to answer our legitimate ancestry block search.
const ANCESTRY_BLOCK_ERROR_REPUTATION_CHANGE: i32 = -(1 << 9);
/// Reputation change when a peer sent us a status message with a different genesis than us.
const GENESIS_MISMATCH_REPUTATION_CHANGE: i32 = i32::min_value() + 1;

#[derive(Debug)]
struct PeerSync<B: BlockT> {
	pub common_number: NumberFor<B>,
	pub best_hash: B::Hash,
	pub best_number: NumberFor<B>,
	pub state: PeerSyncState<B>,
	pub recently_announced: VecDeque<B::Hash>,
}

#[derive(Debug)]
/// Peer sync status.
pub(crate) struct PeerInfo<B: BlockT> {
	/// Their best block hash.
	pub best_hash: B::Hash,
	/// Their best block number.
	pub best_number: NumberFor<B>,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum AncestorSearchState<B: BlockT> {
	/// Use exponential backoff to find an ancestor, then switch to binary search.
	/// We keep track of the exponent.
	ExponentialBackoff(NumberFor<B>),
	/// Using binary search to find the best ancestor.
	/// We keep track of left and right bounds.
	BinarySearch(NumberFor<B>, NumberFor<B>),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum PeerSyncState<B: BlockT> {
	AncestorSearch(NumberFor<B>, AncestorSearchState<B>),
	Available,
	DownloadingNew(NumberFor<B>),
	DownloadingStale(B::Hash),
	DownloadingJustification(B::Hash),
}

/// Pending justification request for the given block (hash and number).
type PendingJustification<B> = (<B as BlockT>::Hash, NumberFor<B>);

/// Manages pending block justification requests. Multiple justifications may be
/// requested for competing forks, or for the same branch at different
/// (increasing) heights. This structure will guarantee that justifications are
/// fetched in-order, and that obsolete changes are pruned (when finalizing a
/// competing fork).
struct PendingJustifications<B: BlockT> {
	justifications: ForkTree<B::Hash, NumberFor<B>, ()>,
	pending_requests: VecDeque<PendingJustification<B>>,
	peer_requests: HashMap<PeerId, PendingJustification<B>>,
	previous_requests: HashMap<PendingJustification<B>, Vec<(PeerId, Instant)>>,
	importing_requests: HashSet<PendingJustification<B>>,
}

impl<B: BlockT> PendingJustifications<B> {
	fn new() -> PendingJustifications<B> {
		PendingJustifications {
			justifications: ForkTree::new(),
			pending_requests: VecDeque::new(),
			peer_requests: HashMap::new(),
			previous_requests: HashMap::new(),
			importing_requests: HashSet::new(),
		}
	}

	/// Dispatches all possible pending requests to the given peers. Peers are
	/// filtered according to the current known best block (i.e. we won't send a
	/// justification request for block #10 to a peer at block #2), and we also
	/// throttle requests to the same peer if a previous justification request
	/// yielded no results.
	fn dispatch(&mut self, peers: &mut HashMap<PeerId, PeerSync<B>>, protocol: &mut Context<B>) {
		if self.pending_requests.is_empty() {
			return;
		}

		let initial_pending_requests = self.pending_requests.len();

		// clean up previous failed requests so we can retry again
		for (_, requests) in self.previous_requests.iter_mut() {
			requests.retain(|(_, instant)| instant.elapsed() < JUSTIFICATION_RETRY_WAIT);
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
			// asking the justification for and to whom we haven't already made
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
				.state = PeerSyncState::DownloadingJustification(request.0);

			trace!(target: "sync", "Requesting justification for block #{} from {}", request.0, peer);
			let request = message::generic::BlockRequest {
				id: 0,
				fields: message::BlockAttributes::JUSTIFICATION,
				from: message::FromBlock::Hash(request.0),
				to: None,
				direction: message::Direction::Ascending,
				max: Some(1),
			};

			protocol.send_block_request(peer, request);
		}

		self.pending_requests.append(&mut unhandled_requests);

		trace!(target: "sync", "Dispatched {} justification requests ({} pending)",
			initial_pending_requests - self.pending_requests.len(),
			self.pending_requests.len(),
		);
	}

	/// Queue a justification request (without dispatching it).
	fn queue_request<F>(
		&mut self,
		justification: &PendingJustification<B>,
		is_descendent_of: F,
	) where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError> {
		match self.justifications.import(justification.0.clone(), justification.1.clone(), (), &is_descendent_of) {
			Ok(true) => {
				// this is a new root so we add it to the current `pending_requests`
				self.pending_requests.push_back((justification.0, justification.1));
			},
			Err(err) => {
				warn!(target: "sync", "Failed to insert requested justification {:?} {:?} into tree: {:?}",
					justification.0,
					justification.1,
					err,
				);
				return;
			},
			_ => {},
		};
	}

	/// Retry any pending request if a peer disconnected.
	fn peer_disconnected(&mut self, who: PeerId) {
		if let Some(request) = self.peer_requests.remove(&who) {
			self.pending_requests.push_front(request);
		}
	}

	/// Process the import of a justification.
	/// Queues a retry in case the import failed.
	fn justification_import_result(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		let request = (hash, number);

		if !self.importing_requests.remove(&request) {
			debug!(target: "sync", "Got justification import result for unknown justification {:?} {:?} request.",
				request.0,
				request.1,
			);

			return;
		};

		if success {
			if self.justifications.finalize_root(&request.0).is_none() {
				warn!(target: "sync", "Imported justification for {:?} {:?} which isn't a root in the tree: {:?}",
					request.0,
					request.1,
					self.justifications.roots().collect::<Vec<_>>(),
				);

				return;
			};

			self.previous_requests.clear();
			self.peer_requests.clear();
			self.pending_requests =
				self.justifications.roots().map(|(h, n, _)| (h.clone(), n.clone())).collect();

			return;
		}
		self.pending_requests.push_front(request);
	}

	/// Processes the response for the request previously sent to the given
	/// peer. Queues a retry in case the given justification
	/// was `None`.
	///
	/// Returns `Some` if this produces a justification that must be imported in the import queue.
	#[must_use]
	fn on_response(
		&mut self,
		who: PeerId,
		justification: Option<Justification>,
	) -> Option<(PeerId, B::Hash, NumberFor<B>, Justification)> {
		// we assume that the request maps to the given response, this is
		// currently enforced by the outer network protocol before passing on
		// messages to chain sync.
		if let Some(request) = self.peer_requests.remove(&who) {
			if let Some(justification) = justification {
				self.importing_requests.insert(request);
				return Some((who, request.0, request.1, justification))
			}

			self.previous_requests
				.entry(request)
				.or_insert(Vec::new())
				.push((who, Instant::now()));

			self.pending_requests.push_front(request);
		}

		None
	}

	/// Removes any pending justification requests for blocks lower than the
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
			// we imported this justification ourselves, so we should get back a response
			// from the import queue through `justification_import_result`
			return Ok(());
		}

		self.justifications.finalize(best_finalized_hash, best_finalized_number, &is_descendent_of)?;

		let roots = self.justifications.roots().collect::<HashSet<_>>();

		self.pending_requests.retain(|(h, n)| roots.contains(&(h, n, &())));
		self.peer_requests.retain(|_, (h, n)| roots.contains(&(h, n, &())));
		self.previous_requests.retain(|(h, n), _| roots.contains(&(h, n, &())));

		Ok(())
	}

	/// Clear all data.
	fn clear(&mut self) {
		self.justifications = ForkTree::new();
		self.pending_requests.clear();
		self.peer_requests.clear();
		self.previous_requests.clear();
	}
}

/// Relay chain sync strategy.
pub struct ChainSync<B: BlockT> {
	genesis_hash: B::Hash,
	peers: HashMap<PeerId, PeerSync<B>>,
	blocks: BlockCollection<B>,
	best_queued_number: NumberFor<B>,
	best_queued_hash: B::Hash,
	required_block_attributes: message::BlockAttributes,
	justifications: PendingJustifications<B>,
	queue_blocks: HashSet<B::Hash>,
	best_importing_number: NumberFor<B>,
}

/// Reported sync state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum SyncState {
	/// Initial sync is complete, keep-up sync is active.
	Idle,
	/// Actively catching up with the chain.
	Downloading
}

/// Syncing status and statistics
#[derive(Clone)]
pub struct Status<B: BlockT> {
	/// Current global sync state.
	pub state: SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<NumberFor<B>>,
	/// Number of peers participating in syncing.
	pub num_peers: u32,
}

impl<B: BlockT> Status<B> {
	/// Whether the synchronization status is doing major downloading work or
	/// is near the head of the chain.
	pub fn is_major_syncing(&self) -> bool {
		match self.state {
			SyncState::Idle => false,
			SyncState::Downloading => true,
		}
	}

	/// Are we all alone?
	pub fn is_offline(&self) -> bool {
		self.num_peers == 0
	}
}

impl<B: BlockT> ChainSync<B> {
	/// Create a new instance. Pass the initial known state of the chain.
	pub(crate) fn new(
		role: Roles,
		info: &ClientInfo<B>,
	) -> Self {
		let mut required_block_attributes = message::BlockAttributes::HEADER | message::BlockAttributes::JUSTIFICATION;
		if role.intersects(Roles::FULL | Roles::AUTHORITY) {
			required_block_attributes |= message::BlockAttributes::BODY;
		}

		ChainSync {
			genesis_hash: info.chain.genesis_hash,
			peers: HashMap::new(),
			blocks: BlockCollection::new(),
			best_queued_hash: info.best_queued_hash.unwrap_or(info.chain.best_hash),
			best_queued_number: info.best_queued_number.unwrap_or(info.chain.best_number),
			justifications: PendingJustifications::new(),
			required_block_attributes,
			queue_blocks: Default::default(),
			best_importing_number: Zero::zero(),
		}
	}

	fn best_seen_block(&self) -> Option<NumberFor<B>> {
		self.peers.values().max_by_key(|p| p.best_number).map(|p| p.best_number)
	}

	fn state(&self, best_seen: &Option<NumberFor<B>>) -> SyncState {
		match best_seen {
			&Some(n) if n > self.best_queued_number && n - self.best_queued_number > As::sa(5) => SyncState::Downloading,
			_ => SyncState::Idle,
		}
	}

	/// Returns the state of the sync of the given peer. Returns `None` if the peer is unknown.
	pub(crate) fn peer_info(&self, who: &PeerId) -> Option<PeerInfo<B>> {
		self.peers.get(who).map(|peer| {
			PeerInfo {
				best_hash: peer.best_hash,
				best_number: peer.best_number,
			}
		})
	}

	/// Returns sync status.
	pub(crate) fn status(&self) -> Status<B> {
		let best_seen = self.best_seen_block();
		let state = self.state(&best_seen);
		Status {
			state: state,
			best_seen_block: best_seen,
			num_peers: self.peers.len() as u32,
		}
	}

	/// Handle new connected peer. Call this method whenever we connect to a new peer.
	pub(crate) fn new_peer(&mut self, protocol: &mut Context<B>, who: PeerId) {
		if let Some(info) = protocol.peer_info(&who) {
			let status = block_status(&*protocol.client(), &self.queue_blocks, info.best_hash);
			match (status, info.best_number) {
				(Err(e), _) => {
					debug!(target:"sync", "Error reading blockchain: {:?}", e);
					protocol.report_peer(who.clone(), BLOCKCHAIN_STATUS_READ_ERROR_REPUTATION_CHANGE);
					protocol.disconnect_peer(who);
				},
				(Ok(BlockStatus::KnownBad), _) => {
					info!("New peer with known bad best block {} ({}).", info.best_hash, info.best_number);
					protocol.report_peer(who.clone(), i32::min_value());
					protocol.disconnect_peer(who);
				},
				(Ok(BlockStatus::Unknown), b) if b == As::sa(0) => {
					info!("New peer with unknown genesis hash {} ({}).", info.best_hash, info.best_number);
					protocol.report_peer(who.clone(), i32::min_value());
					protocol.disconnect_peer(who);
				},
				(Ok(BlockStatus::Unknown), _) if self.queue_blocks.len() > MAJOR_SYNC_BLOCKS => {
					// when actively syncing the common point moves too fast.
					debug!(target:"sync", "New peer with unknown best hash {} ({}), assuming common block.", self.best_queued_hash, self.best_queued_number);
					self.peers.insert(who, PeerSync {
						common_number: self.best_queued_number,
						best_hash: info.best_hash,
						best_number: info.best_number,
						state: PeerSyncState::Available,
						recently_announced: Default::default(),
					});
				}
				(Ok(BlockStatus::Unknown), _) => {
					let our_best = self.best_queued_number;
					if our_best > As::sa(0) {
						let common_best = ::std::cmp::min(our_best, info.best_number);
						debug!(target:"sync", "New peer with unknown best hash {} ({}), searching for common ancestor.", info.best_hash, info.best_number);
						self.peers.insert(who.clone(), PeerSync {
							common_number: As::sa(0),
							best_hash: info.best_hash,
							best_number: info.best_number,
							state: PeerSyncState::AncestorSearch(common_best, AncestorSearchState::ExponentialBackoff(As::sa(1))),
							recently_announced: Default::default(),
						});
						Self::request_ancestry(protocol, who, common_best)
					} else {
						// We are at genesis, just start downloading
						debug!(target:"sync", "New peer with best hash {} ({}).", info.best_hash, info.best_number);
						self.peers.insert(who.clone(), PeerSync {
							common_number: As::sa(0),
							best_hash: info.best_hash,
							best_number: info.best_number,
							state: PeerSyncState::Available,
							recently_announced: Default::default(),
						});
						self.download_new(protocol, who)
					}
				},
				(Ok(BlockStatus::Queued), _) | (Ok(BlockStatus::InChainWithState), _) | (Ok(BlockStatus::InChainPruned), _) => {
					debug!(target:"sync", "New peer with known best hash {} ({}).", info.best_hash, info.best_number);
					self.peers.insert(who.clone(), PeerSync {
						common_number: info.best_number,
						best_hash: info.best_hash,
						best_number: info.best_number,
						state: PeerSyncState::Available,
						recently_announced: Default::default(),
					});
				}
			}
		}
	}

	fn handle_ancestor_search_state(
		state: AncestorSearchState<B>,
		curr_block_num: NumberFor<B>,
		block_hash_match: bool,
	) -> Option<(AncestorSearchState<B>, NumberFor<B>)> {
		match state {
			AncestorSearchState::ExponentialBackoff(next_distance_to_tip) => {
				if block_hash_match && next_distance_to_tip == As::sa(1) {
					// We found the ancestor in the first step so there is no need to execute binary search.
					return None;
				}
				if block_hash_match {
					let left = curr_block_num;
					let right = left + next_distance_to_tip / As::sa(2);
					let middle = left + (right - left) / As::sa(2);
					Some((AncestorSearchState::BinarySearch(left, right), middle))
				} else {
					let next_block_num = curr_block_num.checked_sub(&next_distance_to_tip).unwrap_or(As::sa(0));
					let next_distance_to_tip = next_distance_to_tip * As::sa(2);
					Some((AncestorSearchState::ExponentialBackoff(next_distance_to_tip), next_block_num))
				}
			},
			AncestorSearchState::BinarySearch(mut left, mut right) => {
				if left >= curr_block_num {
					return None;
				}
				if block_hash_match {
					left = curr_block_num;
				} else {
					right = curr_block_num;
				}
				assert!(right >= left);
				let middle = left + (right - left) / As::sa(2);
				Some((AncestorSearchState::BinarySearch(left, right), middle))
			},
		}
	}

	/// Handle a response from the remote to a block request that we made.
	///
	/// `request` must be the original request that triggered `response`.
	///
	/// If this corresponds to a valid block, this outputs the block that must be imported in the
	/// import queue.
	#[must_use]
	pub(crate) fn on_block_data(
		&mut self,
		protocol: &mut Context<B>,
		who: PeerId,
		request: message::BlockRequest<B>,
		response: message::BlockResponse<B>
	) -> Option<(BlockOrigin, Vec<IncomingBlock<B>>)> {
		let new_blocks: Vec<IncomingBlock<B>> = if let Some(ref mut peer) = self.peers.get_mut(&who) {
			let mut blocks = response.blocks;
			if request.direction == message::Direction::Descending {
				trace!(target: "sync", "Reversing incoming block list");
				blocks.reverse();
			}
			let peer_state = peer.state.clone();
			match peer_state {
				PeerSyncState::DownloadingNew(start_block) => {
					self.blocks.clear_peer_download(&who);
					peer.state = PeerSyncState::Available;
					self.blocks.insert(start_block, blocks, who);
					self.blocks
						.drain(self.best_queued_number + As::sa(1))
						.into_iter()
						.map(|block_data| {
							IncomingBlock {
								hash: block_data.block.hash,
								header: block_data.block.header,
								body: block_data.block.body,
								justification: block_data.block.justification,
								origin: block_data.origin,
							}
						}).collect()
				},
				PeerSyncState::DownloadingStale(_) => {
					peer.state = PeerSyncState::Available;
					blocks.into_iter().map(|b| {
						IncomingBlock {
							hash: b.hash,
							header: b.header,
							body: b.body,
							justification: b.justification,
							origin: Some(who.clone()),
						}
					}).collect()
				},
				PeerSyncState::AncestorSearch(num, state) => {
					let block_hash_match = match (blocks.get(0), protocol.client().block_hash(num)) {
						(Some(ref block), Ok(maybe_our_block_hash)) => {
							trace!(target: "sync", "Got ancestry block #{} ({}) from peer {}", num, block.hash, who);
							maybe_our_block_hash.map_or(false, |x| x == block.hash)
						},
						(None, _) => {
							debug!(target: "sync", "Invalid response when searching for ancestor from {}", who);
							protocol.report_peer(who.clone(), i32::min_value());
							protocol.disconnect_peer(who);
							return None
						},
						(_, Err(e)) => {
							info!("Error answering legitimate blockchain query: {:?}", e);
							protocol.report_peer(who.clone(), ANCESTRY_BLOCK_ERROR_REPUTATION_CHANGE);
							protocol.disconnect_peer(who);
							return None
						},
					};
					if block_hash_match && peer.common_number < num {
						peer.common_number = num;
					}
					if !block_hash_match && num == As::sa(0) {
						trace!(target:"sync", "Ancestry search: genesis mismatch for peer {}", who);
						protocol.report_peer(who.clone(), GENESIS_MISMATCH_REPUTATION_CHANGE);
						protocol.disconnect_peer(who);
						return None
					}
					if let Some((next_state, next_block_num)) = Self::handle_ancestor_search_state(state, num, block_hash_match) {
						peer.state = PeerSyncState::AncestorSearch(next_block_num, next_state);
						Self::request_ancestry(protocol, who, next_block_num);
						return None
					} else {
						peer.state = PeerSyncState::Available;
						vec![]
					}
				},
				PeerSyncState::Available | PeerSyncState::DownloadingJustification(..) => Vec::new(),
			}
		} else {
			Vec::new()
		};

		let is_recent = new_blocks
			.first()
			.map(|block| self.peers.iter().any(|(_, peer)| peer.recently_announced.contains(&block.hash)))
			.unwrap_or(false);
		let origin = if is_recent { BlockOrigin::NetworkBroadcast } else { BlockOrigin::NetworkInitialSync };

		if let Some((hash, number)) = new_blocks.last()
			.and_then(|b| b.header.as_ref().map(|h| (b.hash.clone(), *h.number())))
		{
			trace!(target:"sync", "Accepted {} blocks ({:?}) with origin {:?}", new_blocks.len(), hash, origin);
			self.block_queued(&hash, number);
		}
		self.maintain_sync(protocol);
		let new_best_importing_number = new_blocks
			.last()
			.and_then(|b| b.header.as_ref().map(|h| h.number().clone()))
			.unwrap_or_else(|| Zero::zero());
		self.queue_blocks
			.extend(new_blocks.iter().map(|b| b.hash.clone()));
		self.best_importing_number = max(new_best_importing_number, self.best_importing_number);
		Some((origin, new_blocks))
	}

	/// Handle a response from the remote to a justification request that we made.
	///
	/// `request` must be the original request that triggered `response`.
	///
	/// Returns `Some` if this produces a justification that must be imported into the import
	/// queue.
	#[must_use]
	pub(crate) fn on_block_justification_data(
		&mut self,
		protocol: &mut Context<B>,
		who: PeerId,
		_request: message::BlockRequest<B>,
		response: message::BlockResponse<B>,
	) -> Option<(PeerId, B::Hash, NumberFor<B>, Justification)> {
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			if let PeerSyncState::DownloadingJustification(hash) = peer.state {
				peer.state = PeerSyncState::Available;

				// we only request one justification at a time
				match response.blocks.into_iter().next() {
					Some(response) => {
						if hash != response.hash {
							info!("Invalid block justification provided by {}: requested: {:?} got: {:?}",
								who, hash, response.hash);
							protocol.report_peer(who.clone(), i32::min_value());
							protocol.disconnect_peer(who);
							return None;
						}

						return self.justifications.on_response(
							who,
							response.justification,
						);
					},
					None => {
						// we might have asked the peer for a justification on a block that we thought it had
						// (regardless of whether it had a justification for it or not).
						trace!(target: "sync", "Peer {:?} provided empty response for justification request {:?}",
							who,
							hash,
						);
						return None;
					},
				}
			}
		}

		self.maintain_sync(protocol);
		None
	}

	/// Call this when a batch of blocks have been processed by the import queue, with or without
	/// errors.
	pub fn blocks_processed(&mut self, processed_blocks: Vec<B::Hash>, has_error: bool) {
		for hash in processed_blocks {
			self.queue_blocks.remove(&hash);
		}
		if has_error {
			self.best_importing_number = Zero::zero();
		}
	}

	/// Maintain the sync process (download new blocks, fetch justifications).
	pub fn maintain_sync(&mut self, protocol: &mut Context<B>) {
		let peers: Vec<PeerId> = self.peers.keys().map(|p| p.clone()).collect();
		for peer in peers {
			self.download_new(protocol, peer);
		}
		self.justifications.dispatch(&mut self.peers, protocol);
	}

	/// Called periodically to perform any time-based actions. Must be called at a regular
	/// interval.
	pub fn tick(&mut self, protocol: &mut Context<B>) {
		self.justifications.dispatch(&mut self.peers, protocol);
	}

	/// Request a justification for the given block.
	///
	/// Uses `protocol` to queue a new justification request and tries to dispatch all pending
	/// requests.
	pub fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>, protocol: &mut Context<B>) {
		self.justifications.queue_request(
			&(*hash, number),
			|base, block| protocol.client().is_descendent_of(base, block),
		);

		self.justifications.dispatch(&mut self.peers, protocol);
	}

	/// Clears all pending justification requests.
	pub fn clear_justification_requests(&mut self) {
		self.justifications.clear();
	}

	/// Call this when a justification has been processed by the import queue, with or without
	/// errors.
	pub fn justification_import_result(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		self.justifications.justification_import_result(hash, number, success);
	}

	/// Notify about successful import of the given block.
	pub fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		trace!(target: "sync", "Block imported successfully {} ({})", number, hash);
	}

	/// Notify about finalization of the given block.
	pub fn on_block_finalized(&mut self, hash: &B::Hash, number: NumberFor<B>, protocol: &mut Context<B>) {
		if let Err(err) = self.justifications.on_block_finalized(
			hash,
			number,
			|base, block| protocol.client().is_descendent_of(base, block),
		) {
			warn!(target: "sync", "Error cleaning up pending justification requests: {:?}", err);
		};
	}

	fn block_queued(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		if number > self.best_queued_number {
			self.best_queued_number = number;
			self.best_queued_hash = *hash;
		}
		// Update common blocks
		for (n, peer) in self.peers.iter_mut() {
			if let PeerSyncState::AncestorSearch(_, _) = peer.state {
				// Abort search.
				peer.state = PeerSyncState::Available;
			}
			trace!(target: "sync", "Updating peer {} info, ours={}, common={}, their best={}", n, number, peer.common_number, peer.best_number);
			if peer.best_number >= number {
				peer.common_number = number;
			} else {
				peer.common_number = peer.best_number;
			}
		}
	}

	/// Sets the new head of chain.
	pub(crate) fn update_chain_info(&mut self, best_header: &B::Header) {
		let hash = best_header.hash();
		self.block_queued(&hash, best_header.number().clone())
	}

	/// Call when a node announces a new block.
	pub(crate) fn on_block_announce(&mut self, protocol: &mut Context<B>, who: PeerId, hash: B::Hash, header: &B::Header) {
		let number = *header.number();
		debug!(target: "sync", "Received block announcement with number {:?}", number);
		if number <= As::sa(0) {
			warn!(target: "sync", "Ignored invalid block announcement from {}: {}", who, hash);
			return;
		}
		let parent_status = block_status(&*protocol.client(), &self.queue_blocks, header.parent_hash().clone()).ok()
			.unwrap_or(BlockStatus::Unknown);
		let known_parent = parent_status != BlockStatus::Unknown;
		let ancient_parent = parent_status == BlockStatus::InChainPruned;

		let known = self.is_known(protocol, &hash);
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			while peer.recently_announced.len() >= ANNOUNCE_HISTORY_SIZE {
				peer.recently_announced.pop_front();
			}
			peer.recently_announced.push_back(hash.clone());
			if number > peer.best_number {
				// update their best block
				peer.best_number = number;
				peer.best_hash = hash;
			}
			if let PeerSyncState::AncestorSearch(_, _) = peer.state {
				return;
			}
			if header.parent_hash() == &self.best_queued_hash || known_parent {
				peer.common_number = number - As::sa(1);
			} else if known {
				peer.common_number = number
			}
		} else {
			return;
		}

		if !(known || self.is_already_downloading(&hash)) {
			let stale = number <= self.best_queued_number;
			if stale {
				if !(known_parent || self.is_already_downloading(header.parent_hash())) {
					if protocol.client().block_status(&BlockId::Number(*header.number()))
						.unwrap_or(BlockStatus::Unknown) == BlockStatus::InChainPruned
					{
						trace!(target: "sync", "Ignored unknown ancient block announced from {}: {} {:?}", who, hash, header);
					} else {
						trace!(target: "sync", "Considering new unknown stale block announced from {}: {} {:?}", who, hash, header);
						self.download_unknown_stale(protocol, who, &hash);
					}
				} else {
					if ancient_parent {
						trace!(target: "sync", "Ignored ancient stale block announced from {}: {} {:?}", who, hash, header);
					} else {
						self.download_stale(protocol, who, &hash);
					}
				}
			} else {
				if ancient_parent {
					trace!(target: "sync", "Ignored ancient block announced from {}: {} {:?}", who, hash, header);
				} else {
					trace!(target: "sync", "Considering new block announced from {}: {} {:?}", who, hash, header);
					self.download_new(protocol, who);
				}
			}
		} else {
			trace!(target: "sync", "Known block announce from {}: {}", who, hash);
		}
	}

	fn is_already_downloading(&self, hash: &B::Hash) -> bool {
		self.peers.iter().any(|(_, p)| p.state == PeerSyncState::DownloadingStale(*hash))
	}

	fn is_known(&self, protocol: &mut Context<B>, hash: &B::Hash) -> bool {
		block_status(&*protocol.client(), &self.queue_blocks, *hash).ok().map_or(false, |s| s != BlockStatus::Unknown)
	}

	/// Call when a peer has disconnected.
	pub(crate) fn peer_disconnected(&mut self, protocol: &mut Context<B>, who: PeerId) {
		self.blocks.clear_peer_download(&who);
		self.peers.remove(&who);
		self.justifications.peer_disconnected(who);
		self.maintain_sync(protocol);
	}

	/// Restart the sync process.
	pub(crate) fn restart(&mut self, protocol: &mut Context<B>) {
		self.queue_blocks.clear();
		self.best_importing_number = Zero::zero();
		self.blocks.clear();
		match protocol.client().info() {
			Ok(info) => {
				self.best_queued_hash = info.best_queued_hash.unwrap_or(info.chain.best_hash);
				self.best_queued_number = info.best_queued_number.unwrap_or(info.chain.best_number);
				debug!(target:"sync", "Restarted with {} ({})", self.best_queued_number, self.best_queued_hash);
			},
			Err(e) => {
				debug!(target:"sync", "Error reading blockchain: {:?}", e);
				self.best_queued_hash = self.genesis_hash;
				self.best_queued_number = As::sa(0);
			}
		}
		let ids: Vec<PeerId> = self.peers.drain().map(|(id, _)| id).collect();
		for id in ids {
			self.new_peer(protocol, id);
		}
	}

	// Download old block with known parent.
	fn download_stale(&mut self, protocol: &mut Context<B>, who: PeerId, hash: &B::Hash) {
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			match peer.state {
				PeerSyncState::Available => {
					let request = message::generic::BlockRequest {
						id: 0,
						fields: self.required_block_attributes.clone(),
						from: message::FromBlock::Hash(*hash),
						to: None,
						direction: message::Direction::Ascending,
						max: Some(1),
					};
					peer.state = PeerSyncState::DownloadingStale(*hash);
					protocol.send_block_request(who, request);
				},
				_ => (),
			}
		}
	}

	// Download old block with unknown parent.
	fn download_unknown_stale(&mut self, protocol: &mut Context<B>, who: PeerId, hash: &B::Hash) {
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			match peer.state {
				PeerSyncState::Available => {
					let request = message::generic::BlockRequest {
						id: 0,
						fields: self.required_block_attributes.clone(),
						from: message::FromBlock::Hash(*hash),
						to: None,
						direction: message::Direction::Descending,
						max: Some(MAX_UNKNOWN_FORK_DOWNLOAD_LEN),
					};
					peer.state = PeerSyncState::DownloadingStale(*hash);
					protocol.send_block_request(who, request);
				},
				_ => (),
			}
		}
	}

	// Issue a request for a peer to download new blocks, if any are available
	fn download_new(&mut self, protocol: &mut Context<B>, who: PeerId) {
		if let Some(ref mut peer) = self.peers.get_mut(&who) {
			// when there are too many blocks in the queue => do not try to download new blocks
			if self.queue_blocks.len() > MAX_IMPORTING_BLOCKS {
				trace!(target: "sync", "Too many blocks in the queue.");
				return;
			}
			match peer.state {
				PeerSyncState::Available => {
					trace!(target: "sync", "Considering new block download from {}, common block is {}, best is {:?}", who, peer.common_number, peer.best_number);
					if let Some(range) = self.blocks.needed_blocks(who.clone(), MAX_BLOCKS_TO_REQUEST, peer.best_number, peer.common_number) {
						trace!(target: "sync", "Requesting blocks from {}, ({} to {})", who, range.start, range.end);
						let request = message::generic::BlockRequest {
							id: 0,
							fields: self.required_block_attributes.clone(),
							from: message::FromBlock::Number(range.start),
							to: None,
							direction: message::Direction::Ascending,
							max: Some((range.end - range.start).as_() as u32),
						};
						peer.state = PeerSyncState::DownloadingNew(range.start);
						protocol.send_block_request(who, request);
					} else {
						trace!(target: "sync", "Nothing to request");
					}
				},
				_ => trace!(target: "sync", "Peer {} is busy", who),
			}
		}
	}

	fn request_ancestry(protocol: &mut Context<B>, who: PeerId, block: NumberFor<B>) {
		trace!(target: "sync", "Requesting ancestry block #{} from {}", block, who);
		let request = message::generic::BlockRequest {
			id: 0,
			fields: message::BlockAttributes::HEADER | message::BlockAttributes::JUSTIFICATION,
			from: message::FromBlock::Number(block),
			to: None,
			direction: message::Direction::Ascending,
			max: Some(1),
		};
		protocol.send_block_request(who, request);
	}
}

/// Get block status, taking into account import queue.
fn block_status<B: BlockT>(
	chain: &crate::chain::Client<B>,
	queue_blocks: &HashSet<B::Hash>,
	hash: B::Hash) -> Result<BlockStatus, ClientError>
{
	if queue_blocks.contains(&hash) {
		return Ok(BlockStatus::Queued);
	}

	chain.block_status(&BlockId::Hash(hash))
}
