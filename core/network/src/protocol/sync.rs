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
use std::ops::Range;
use std::collections::{HashMap, VecDeque};
use log::{debug, trace, warn, info, error};
use crate::protocol::PeerInfo as ProtocolPeerInfo;
use network_libp2p::PeerId;
use client::{BlockStatus, ClientInfo};
use consensus::{BlockOrigin, import_queue::{IncomingBlock, SharedFinalityProofRequestBuilder}};
use client::error::Error as ClientError;
use blocks::BlockCollection;
use extra_requests::ExtraRequestsAggregator;
use runtime_primitives::traits::{
	Block as BlockT, Header as HeaderT, NumberFor, Zero, One,
	CheckedSub, SaturatedConversion
};
use runtime_primitives::{Justification, generic::BlockId};
use crate::message;
use crate::config::Roles;
use std::collections::HashSet;

mod blocks;
mod extra_requests;

// Maximum blocks to request in a single packet.
const MAX_BLOCKS_TO_REQUEST: usize = 128;
// Maximum blocks to store in the import queue.
const MAX_IMPORTING_BLOCKS: usize = 2048;
// Number of blocks in the queue that prevents ancestry search.
const MAJOR_SYNC_BLOCKS: usize = 5;
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

/// Context for a network-specific handler.
pub trait Context<B: BlockT> {
	/// Get a reference to the client.
	fn client(&self) -> &dyn crate::chain::Client<B>;

	/// Adjusts the reputation of the peer. Use this to point out that a peer has been malign or
	/// irresponsible or appeared lazy.
	fn report_peer(&mut self, who: PeerId, reputation: i32);

	/// Force disconnecting from a peer. Use this when a peer misbehaved.
	fn disconnect_peer(&mut self, who: PeerId);

	/// Request a finality proof from a peer.
	fn send_finality_proof_request(&mut self, who: PeerId, request: message::FinalityProofRequest<B::Hash>);

	/// Request a block from a peer.
	fn send_block_request(&mut self, who: PeerId, request: message::BlockRequest<B>);
}

#[derive(Debug)]
pub(crate) struct PeerSync<B: BlockT> {
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
pub(crate) enum AncestorSearchState<B: BlockT> {
	/// Use exponential backoff to find an ancestor, then switch to binary search.
	/// We keep track of the exponent.
	ExponentialBackoff(NumberFor<B>),
	/// Using binary search to find the best ancestor.
	/// We keep track of left and right bounds.
	BinarySearch(NumberFor<B>, NumberFor<B>),
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub(crate) enum PeerSyncState<B: BlockT> {
	AncestorSearch(NumberFor<B>, AncestorSearchState<B>),
	Available,
	DownloadingNew(NumberFor<B>),
	DownloadingStale(B::Hash),
	DownloadingJustification(B::Hash),
	DownloadingFinalityProof(B::Hash),
}

/// Relay chain sync strategy.
pub struct ChainSync<B: BlockT> {
	_genesis_hash: B::Hash,
	peers: HashMap<PeerId, PeerSync<B>>,
	blocks: BlockCollection<B>,
	best_queued_number: NumberFor<B>,
	best_queued_hash: B::Hash,
	role: Roles,
	required_block_attributes: message::BlockAttributes,
	extra_requests: ExtraRequestsAggregator<B>,
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
		if role.is_full() {
			required_block_attributes |= message::BlockAttributes::BODY;
		}

		ChainSync {
			_genesis_hash: info.chain.genesis_hash,
			peers: HashMap::new(),
			blocks: BlockCollection::new(),
			best_queued_hash: info.chain.best_hash,
			best_queued_number: info.chain.best_number,
			extra_requests: ExtraRequestsAggregator::new(),
			role,
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
			&Some(n) if n > self.best_queued_number && n - self.best_queued_number > 5.into() => SyncState::Downloading,
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
			state,
			best_seen_block: best_seen,
			num_peers: self.peers.len() as u32,
		}
	}

	/// Handle new connected peer. Call this method whenever we connect to a new peer.
	pub(crate) fn new_peer(
		&mut self,
		protocol: &mut dyn Context<B>,
		who: PeerId,
		info: ProtocolPeerInfo<B>
	) {
		// there's nothing sync can get from the node that has no blockchain data
		// (the opposite is not true, but all requests are served at protocol level)
		if !info.roles.is_full() {
			return;
		}

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
			(Ok(BlockStatus::Unknown), b) if b.is_zero() => {
				info!("New peer with unknown genesis hash {} ({}).", info.best_hash, info.best_number);
				protocol.report_peer(who.clone(), i32::min_value());
				protocol.disconnect_peer(who);
			},
			(Ok(BlockStatus::Unknown), _) if self.queue_blocks.len() > MAJOR_SYNC_BLOCKS => {
				// when actively syncing the common point moves too fast.
				debug!(
					target:"sync",
					"New peer with unknown best hash {} ({}), assuming common block.",
					self.best_queued_hash,
					self.best_queued_number
				);
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
				if our_best.is_zero() {
					// We are at genesis, just start downloading
					debug!(target:"sync", "New peer with best hash {} ({}).", info.best_hash, info.best_number);
					self.peers.insert(who.clone(), PeerSync {
						common_number: Zero::zero(),
						best_hash: info.best_hash,
						best_number: info.best_number,
						state: PeerSyncState::Available,
						recently_announced: Default::default(),
					});
					self.download_new(protocol, who)
				} else {
					let common_best = ::std::cmp::min(our_best, info.best_number);
					debug!(target:"sync",
						"New peer with unknown best hash {} ({}), searching for common ancestor.",
						info.best_hash,
						info.best_number
					);
					self.peers.insert(who.clone(), PeerSync {
						common_number: Zero::zero(),
						best_hash: info.best_hash,
						best_number: info.best_number,
						state: PeerSyncState::AncestorSearch(
							common_best,
							AncestorSearchState::ExponentialBackoff(One::one())
						),
						recently_announced: Default::default(),
					});
					Self::request_ancestry(protocol, who, common_best)
				}
			},
			(Ok(BlockStatus::Queued), _) |
			(Ok(BlockStatus::InChainWithState), _) |
			(Ok(BlockStatus::InChainPruned), _) => {
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

	fn handle_ancestor_search_state(
		state: AncestorSearchState<B>,
		curr_block_num: NumberFor<B>,
		block_hash_match: bool,
	) -> Option<(AncestorSearchState<B>, NumberFor<B>)> {
		let two = <NumberFor<B>>::one() + <NumberFor<B>>::one();
		match state {
			AncestorSearchState::ExponentialBackoff(next_distance_to_tip) => {
				if block_hash_match && next_distance_to_tip == One::one() {
					// We found the ancestor in the first step so there is no need to execute binary search.
					return None;
				}
				if block_hash_match {
					let left = curr_block_num;
					let right = left + next_distance_to_tip / two;
					let middle = left + (right - left) / two;
					Some((AncestorSearchState::BinarySearch(left, right), middle))
				} else {
					let next_block_num = curr_block_num.checked_sub(&next_distance_to_tip)
						.unwrap_or_else(Zero::zero);
					let next_distance_to_tip = next_distance_to_tip * two;
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
				let middle = left + (right - left) / two;
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
		protocol: &mut dyn Context<B>,
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
						.drain(self.best_queued_number + One::one())
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
					if !block_hash_match && num.is_zero() {
						trace!(target:"sync", "Ancestry search: genesis mismatch for peer {}", who);
						protocol.report_peer(who.clone(), GENESIS_MISMATCH_REPUTATION_CHANGE);
						protocol.disconnect_peer(who);
						return None
					}
					if let Some((next_state, next_block_num)) =
						Self::handle_ancestor_search_state(state, num, block_hash_match) {
						peer.state = PeerSyncState::AncestorSearch(next_block_num, next_state);
						Self::request_ancestry(protocol, who, next_block_num);
						return None
					} else {
						peer.state = PeerSyncState::Available;
						vec![]
					}
				},
				PeerSyncState::Available |
				PeerSyncState::DownloadingJustification(..) |
				PeerSyncState::DownloadingFinalityProof(..) => Vec::new(),
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
		protocol: &mut dyn Context<B>,
		who: PeerId,
		_request: message::BlockRequest<B>,
		response: message::BlockResponse<B>,
	) -> Option<(PeerId, B::Hash, NumberFor<B>, Justification)> {
		let peer = if let Some(peer) = self.peers.get_mut(&who) {
			peer
		} else {
			error!(target: "sync", "Called on_block_justification_data with a bad peer ID");
			return None;
		};

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

					return self.extra_requests.justifications().on_response(
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

		self.maintain_sync(protocol);
		None
	}

	/// Handle new finality proof data.
	pub(crate) fn on_block_finality_proof_data(
		&mut self,
		protocol: &mut dyn Context<B>,
		who: PeerId,
		response: message::FinalityProofResponse<B::Hash>,
	) -> Option<(PeerId, B::Hash, NumberFor<B>, Vec<u8>)> {
		let peer = if let Some(peer) = self.peers.get_mut(&who) {
			peer
		} else {
			error!(target: "sync", "Called on_block_finality_proof_data with a bad peer ID");
			return None;
		};

		if let PeerSyncState::DownloadingFinalityProof(hash) = peer.state {
			peer.state = PeerSyncState::Available;

			// we only request one finality proof at a time
			if hash != response.block {
				info!(
					"Invalid block finality proof provided: requested: {:?} got: {:?}",
					hash,
					response.block,
				);

				protocol.report_peer(who.clone(), i32::min_value());
				protocol.disconnect_peer(who);
				return None;
			}

			return self.extra_requests.finality_proofs().on_response(
				who,
				response.proof,
			);
		}

		self.maintain_sync(protocol);
		None
	}

	/// A batch of blocks have been processed, with or without errors.
	/// Call this when a batch of blocks have been processed by the import queue, with or without
	/// errors.
	pub fn blocks_processed(&mut self, protocol: &mut Context<B>, processed_blocks: Vec<B::Hash>, has_error: bool) {
		for hash in processed_blocks {
			self.queue_blocks.remove(&hash);
		}
		if has_error {
			self.best_importing_number = Zero::zero();
		}
		self.maintain_sync(protocol)
	}

	/// Maintain the sync process (download new blocks, fetch justifications).
	fn maintain_sync(&mut self, protocol: &mut dyn Context<B>) {
		let peers: Vec<PeerId> = self.peers.keys().map(|p| p.clone()).collect();
		for peer in peers {
			self.download_new(protocol, peer);
		}
		self.extra_requests.dispatch(&mut self.peers, protocol);
	}

	/// Called periodically to perform any time-based actions. Must be called at a regular
	/// interval.
	pub fn tick(&mut self, protocol: &mut dyn Context<B>) {
		self.extra_requests.dispatch(&mut self.peers, protocol);
	}

	/// Request a justification for the given block.
	///
	/// Uses `protocol` to queue a new justification request and tries to dispatch all pending
	/// requests.
	pub fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>, protocol: &mut dyn Context<B>) {
		self.extra_requests.justifications().queue_request(
			(*hash, number),
			|base, block| protocol.client().is_descendent_of(base, block),
		);

		self.extra_requests.justifications().dispatch(&mut self.peers, protocol);
	}

	/// Clears all pending justification requests.
	pub fn clear_justification_requests(&mut self) {
		self.extra_requests.justifications().clear();
	}

	/// Call this when a justification has been processed by the import queue, with or without
	/// errors.
	pub fn justification_import_result(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		let finalization_result = if success { Ok((hash, number)) } else { Err(()) };
		if !self.extra_requests.justifications().on_import_result((hash, number), finalization_result) {
			debug!(target: "sync", "Got justification import result for unknown justification {:?} {:?} request.",
				hash,
				number,
			);
		}
	}

	/// Request a finality proof for the given block.
	///
	/// Queues a new finality proof request and tries to dispatch all pending requests.
	pub fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>, protocol: &mut dyn Context<B>) {
		self.extra_requests.finality_proofs().queue_request(
			(*hash, number),
			|base, block| protocol.client().is_descendent_of(base, block),
		);

		self.extra_requests.finality_proofs().dispatch(&mut self.peers, protocol);
	}

	pub fn finality_proof_import_result(
		&mut self,
		request_block: (B::Hash, NumberFor<B>),
		finalization_result: Result<(B::Hash, NumberFor<B>), ()>,
	) {
		self.extra_requests.finality_proofs().on_import_result(request_block, finalization_result);
	}

	pub fn set_finality_proof_request_builder(&mut self, request_builder: SharedFinalityProofRequestBuilder<B>) {
		self.extra_requests.finality_proofs().essence().0 = Some(request_builder);
	}

	/// Notify about successful import of the given block.
	pub fn block_imported(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		trace!(target: "sync", "Block imported successfully {} ({})", number, hash);
	}

	/// Notify about finalization of the given block.
	pub fn on_block_finalized(&mut self, hash: &B::Hash, number: NumberFor<B>, protocol: &mut dyn Context<B>) {
		if let Err(err) = self.extra_requests.on_block_finalized(
			hash,
			number,
			&|base, block| protocol.client().is_descendent_of(base, block),
		) {
			warn!(target: "sync", "Error cleaning up pending extra data requests: {:?}", err);
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
			let new_common_number = if peer.best_number >= number {
				number
			} else {
				peer.best_number
			};
			trace!(
				target: "sync",
				"Updating peer {} info, ours={}, common={}->{}, their best={}",
				n,
				number,
				peer.common_number,
				new_common_number,
				peer.best_number,
			);
			peer.common_number = new_common_number;
		}
	}

	/// Sets the new head of chain.
	pub(crate) fn update_chain_info(&mut self, best_header: &B::Header) {
		let hash = best_header.hash();
		self.block_queued(&hash, best_header.number().clone())
	}

	/// Call when a node announces a new block.
	///
	/// If true is returned, then the caller MUST try to import passed header (call `on_block_data).
	/// The network request isn't sent in this case.
	#[must_use]
	pub(crate) fn on_block_announce(
		&mut self,
		protocol: &mut dyn Context<B>,
		who: PeerId,
		hash: B::Hash,
		header: &B::Header,
	) -> bool {
		let number = *header.number();
		debug!(target: "sync", "Received block announcement with number {:?}", number);
		if number.is_zero() {
			warn!(target: "sync", "Ignored invalid block announcement from {}: {}", who, hash);
			return false;
		}
		let parent_status = block_status(&*protocol.client(), &self.queue_blocks, header.parent_hash().clone()).ok()
			.unwrap_or(BlockStatus::Unknown);
		let known_parent = parent_status != BlockStatus::Unknown;
		let ancient_parent = parent_status == BlockStatus::InChainPruned;

		let known = self.is_known(protocol, &hash);
		let peer = if let Some(peer) = self.peers.get_mut(&who) {
			peer
		} else {
			error!(target: "sync", "Called on_block_announce with a bad peer ID");
			return false;
		};
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
			return false;
		}
		if header.parent_hash() == &self.best_queued_hash || known_parent {
			peer.common_number = number - One::one();
		} else if known {
			peer.common_number = number
		}

		// known block case
		if known || self.is_already_downloading(&hash) {
			trace!(target: "sync", "Known block announce from {}: {}", who, hash);
			return false;
		}

		// stale block case
		let requires_additional_data = !self.role.is_light();
		let stale = number <= self.best_queued_number;
		if stale {
			if !(known_parent || self.is_already_downloading(header.parent_hash())) {
				if protocol.client().block_status(&BlockId::Number(*header.number()))
					.unwrap_or(BlockStatus::Unknown) == BlockStatus::InChainPruned
				{
					trace!(
						target: "sync",
						"Ignored unknown ancient block announced from {}: {} {:?}",
						who, hash, header
					);
					return false;
				}

				trace!(
					target: "sync",
					"Considering new unknown stale block announced from {}: {} {:?}",
					who, hash, header
				);
				let request = self.download_unknown_stale(&who, &hash);
				match request {
					Some(request) => if requires_additional_data {
						protocol.send_block_request(who, request);
						return false;
					} else {
						return true;
					},
					None => return false,
				}
			} else {
				if ancient_parent {
					trace!(
						target: "sync",
						"Ignored ancient stale block announced from {}: {} {:?}",
						who, hash, header
					);
					return false;
				}

				let request = self.download_stale(&who, &hash);
				match request {
					Some(request) => if requires_additional_data {
						protocol.send_block_request(who, request);
						return false;
					} else {
						return true;
					},
					None => return false,
				}
			}
		}

		if ancient_parent {
			trace!(target: "sync", "Ignored ancient block announced from {}: {} {:?}", who, hash, header);
			return false;
		}

		trace!(target: "sync", "Considering new block announced from {}: {} {:?}", who, hash, header);
		let (range, request) = match self.select_new_blocks(who.clone()) {
			Some((range, request)) => (range, request),
			None => return false,
		};
		let is_required_data_available =
			!requires_additional_data &&
			range.end - range.start == One::one() &&
			range.start == *header.number();
		if !is_required_data_available {
			protocol.send_block_request(who, request);
			return false;
		}

		true
	}

	fn is_already_downloading(&self, hash: &B::Hash) -> bool {
		self.peers.iter().any(|(_, p)| p.state == PeerSyncState::DownloadingStale(*hash))
	}

	fn is_known(&self, protocol: &mut dyn Context<B>, hash: &B::Hash) -> bool {
		block_status(&*protocol.client(), &self.queue_blocks, *hash).ok().map_or(false, |s| s != BlockStatus::Unknown)
	}

	/// Call when a peer has disconnected.
	pub(crate) fn peer_disconnected(&mut self, protocol: &mut dyn Context<B>, who: PeerId) {
		self.blocks.clear_peer_download(&who);
		self.peers.remove(&who);
		self.extra_requests.peer_disconnected(who);
		self.maintain_sync(protocol);
	}

	/// Restart the sync process.
	pub(crate) fn restart(
		&mut self,
		protocol: &mut dyn Context<B>,
		mut peer_info: impl FnMut(&PeerId) -> Option<ProtocolPeerInfo<B>>
	) {
		self.queue_blocks.clear();
		self.best_importing_number = Zero::zero();
		self.blocks.clear();
		let info = protocol.client().info();
		self.best_queued_hash = info.chain.best_hash;
		self.best_queued_number = info.chain.best_number;
		debug!(target:"sync", "Restarted with {} ({})", self.best_queued_number, self.best_queued_hash);
		let ids: Vec<PeerId> = self.peers.drain().map(|(id, _)| id).collect();
		for id in ids {
			if let Some(info) = peer_info(&id) {
				self.new_peer(protocol, id, info);
			}
		}
	}

	// Download old block with known parent.
	fn download_stale(
		&mut self,
		who: &PeerId,
		hash: &B::Hash,
	) -> Option<message::BlockRequest<B>> {
		let peer = self.peers.get_mut(who)?;
		match peer.state {
			PeerSyncState::Available => {
				peer.state = PeerSyncState::DownloadingStale(*hash);
				Some(message::generic::BlockRequest {
					id: 0,
					fields: self.required_block_attributes.clone(),
					from: message::FromBlock::Hash(*hash),
					to: None,
					direction: message::Direction::Ascending,
					max: Some(1),
				})
			},
			_ => None,
		}
	}

	// Download old block with unknown parent.
	fn download_unknown_stale(
		&mut self,
		who: &PeerId,
		hash: &B::Hash,
	) -> Option<message::BlockRequest<B>> {
		let peer = self.peers.get_mut(who)?;
		match peer.state {
			PeerSyncState::Available => {
				peer.state = PeerSyncState::DownloadingStale(*hash);
				Some(message::generic::BlockRequest {
					id: 0,
					fields: self.required_block_attributes.clone(),
					from: message::FromBlock::Hash(*hash),
					to: None,
					direction: message::Direction::Descending,
					max: Some(MAX_UNKNOWN_FORK_DOWNLOAD_LEN),
				})
			},
			_ => None,
		}
	}

	// Issue a request for a peer to download new blocks, if any are available.
	fn download_new(&mut self, protocol: &mut dyn Context<B>, who: PeerId) {
		if let Some((_, request)) = self.select_new_blocks(who.clone()) {
			protocol.send_block_request(who, request);
		}
	}

	// Select a range of NEW blocks to download from peer.
	fn select_new_blocks(&mut self, who: PeerId) -> Option<(Range<NumberFor<B>>, message::BlockRequest<B>)> {
		// when there are too many blocks in the queue => do not try to download new blocks
		if self.queue_blocks.len() > MAX_IMPORTING_BLOCKS {
			trace!(target: "sync", "Too many blocks in the queue.");
			return None;
		}

		let peer = self.peers.get_mut(&who)?;
		match peer.state {
			PeerSyncState::Available => {
				trace!(
					target: "sync",
					"Considering new block download from {}, common block is {}, best is {:?}",
					who,
					peer.common_number,
					peer.best_number,
				);
				let range = self.blocks.needed_blocks(
					who.clone(),
					MAX_BLOCKS_TO_REQUEST,
					peer.best_number,
					peer.common_number
				);
				match range {
					Some(range) => {
						trace!(target: "sync", "Requesting blocks from {}, ({} to {})", who, range.start, range.end);
						let from = message::FromBlock::Number(range.start);
						let max = Some((range.end - range.start).saturated_into::<u32>());
						peer.state = PeerSyncState::DownloadingNew(range.start);
						Some((
							range,
							message::generic::BlockRequest {
								id: 0,
								fields: self.required_block_attributes.clone(),
								from,
								to: None,
								direction: message::Direction::Ascending,
								max,
							},
						))
					},
					None => {
						trace!(target: "sync", "Nothing to request");
						None
					},
				}
			},
			_ => {
				trace!(target: "sync", "Peer {} is busy", who);
				None
			},
		}
	}

	fn request_ancestry(protocol: &mut dyn Context<B>, who: PeerId, block: NumberFor<B>) {
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
	chain: &dyn crate::chain::Client<B>,
	queue_blocks: &HashSet<B::Hash>,
	hash: B::Hash) -> Result<BlockStatus, ClientError>
{
	if queue_blocks.contains(&hash) {
		return Ok(BlockStatus::Queued);
	}

	chain.block_status(&BlockId::Hash(hash))
}
