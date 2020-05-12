// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.
//
// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.
//
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
//! order to update it.
//!

use codec::Encode;
use blocks::BlockCollection;
use sp_blockchain::{Error as ClientError, Info as BlockchainInfo, HeaderMetadata};
use sp_consensus::{BlockOrigin, BlockStatus,
	block_validation::{BlockAnnounceValidator, Validation},
	import_queue::{IncomingBlock, BlockImportResult, BlockImportError}
};
use crate::{
	config::BoxFinalityProofRequestBuilder,
	protocol::message::{self, generic::FinalityProofRequest, BlockAnnounce, BlockAttributes, BlockRequest, BlockResponse,
	FinalityProofResponse, Roles},
};
use either::Either;
use extra_requests::ExtraRequests;
use libp2p::PeerId;
use log::{debug, trace, warn, info, error};
use sp_runtime::{
	Justification,
	generic::BlockId,
	traits::{Block as BlockT, Header, NumberFor, Zero, One, CheckedSub, SaturatedConversion, Hash, HashFor}
};
use std::{fmt, ops::Range, collections::{HashMap, HashSet, VecDeque}, sync::Arc};

mod blocks;
mod extra_requests;

/// Maximum blocks to request in a single packet.
const MAX_BLOCKS_TO_REQUEST: usize = 128;

/// Maximum blocks to store in the import queue.
const MAX_IMPORTING_BLOCKS: usize = 2048;

/// Maximum blocks to download ahead of any gap.
const MAX_DOWNLOAD_AHEAD: u32 = 2048;

/// We use a heuristic that with a high likelihood, by the time
/// `MAJOR_SYNC_BLOCKS` have been imported we'll be on the same
/// chain as (or at least closer to) the peer so we want to delay
/// the ancestor search to not waste time doing that when we are
/// so far behind.
const MAJOR_SYNC_BLOCKS: u8 = 5;

/// Number of recently announced blocks to track for each peer.
const ANNOUNCE_HISTORY_SIZE: usize = 64;

mod rep {
	use sc_peerset::ReputationChange as Rep;
	/// Reputation change when a peer sent us a message that led to a
	/// database read error.
	pub const BLOCKCHAIN_READ_ERROR: Rep = Rep::new(-(1 << 16), "DB Error");

	/// Reputation change when a peer sent us a status message with a different
	/// genesis than us.
	pub const GENESIS_MISMATCH: Rep = Rep::new(i32::min_value(), "Genesis mismatch");

	/// Reputation change for peers which send us a block with an incomplete header.
	pub const INCOMPLETE_HEADER: Rep = Rep::new(-(1 << 20), "Incomplete header");

	/// Reputation change for peers which send us a block which we fail to verify.
	pub const VERIFICATION_FAIL: Rep = Rep::new(-(1 << 29), "Block verification failed");

	/// Reputation change for peers which send us a known bad block.
	pub const BAD_BLOCK: Rep = Rep::new(-(1 << 29), "Bad block");

	/// Peer did not provide us with advertised block data.
	pub const NO_BLOCK: Rep = Rep::new(-(1 << 29), "No requested block data");

	/// Reputation change for peers which send us a known block.
	pub const KNOWN_BLOCK: Rep = Rep::new(-(1 << 29), "Duplicate block");

	/// Reputation change for peers which send us a block with bad justifications.
	pub const BAD_JUSTIFICATION: Rep = Rep::new(-(1 << 16), "Bad justification");

	/// Reputation change for peers which send us a block with bad finality proof.
	pub const BAD_FINALITY_PROOF: Rep = Rep::new(-(1 << 16), "Bad finality proof");

	/// Reputation change when a peer sent us invlid ancestry result.
	pub const UNKNOWN_ANCESTOR:Rep = Rep::new(-(1 << 16), "DB Error");
}

enum PendingRequests {
	Some(HashSet<PeerId>),
	All,
}

impl PendingRequests {
	fn add(&mut self, id: &PeerId) {
		match self {
			PendingRequests::Some(set) => {
				set.insert(id.clone());
			}
			PendingRequests::All => {},
		}
	}

	fn take(&mut self) -> PendingRequests {
		std::mem::take(self)
	}

	fn set_all(&mut self) {
		*self = PendingRequests::All;
	}

	fn contains(&self, id: &PeerId) -> bool {
		match self {
			PendingRequests::Some(set) => set.contains(id),
			PendingRequests::All => true,
		}
	}

	fn is_empty(&self) -> bool {
		match self {
			PendingRequests::Some(set) => set.is_empty(),
			PendingRequests::All => false,
		}
	}
}

impl Default for PendingRequests {
	fn default() -> Self {
		PendingRequests::Some(HashSet::default())
	}
}

/// The main data structure which contains all the state for a chains
/// active syncing strategy.
pub struct ChainSync<B: BlockT> {
	/// Chain client.
	client: Arc<dyn crate::chain::Client<B>>,
	/// The active peers that we are using to sync and their PeerSync status
	peers: HashMap<PeerId, PeerSync<B>>,
	/// A `BlockCollection` of blocks that are being downloaded from peers
	blocks: BlockCollection<B>,
	/// The best block number in our queue of blocks to import
	best_queued_number: NumberFor<B>,
	/// The best block hash in our queue of blocks to import
	best_queued_hash: B::Hash,
	/// The role of this node, e.g. light or full
	role: Roles,
	/// What block attributes we require for this node, usually derived from
	/// what role we are, but could be customized
	required_block_attributes: message::BlockAttributes,
	/// Any extra finality proof requests.
	extra_finality_proofs: ExtraRequests<B>,
	/// Any extra justification requests.
	extra_justifications: ExtraRequests<B>,
	/// A set of hashes of blocks that are being downloaded or have been
	/// downloaded and are queued for import.
	queue_blocks: HashSet<B::Hash>,
	/// The best block number that was successfully imported into the chain.
	/// This can not decrease.
	best_imported_number: NumberFor<B>,
	/// Finality proof handler.
	request_builder: Option<BoxFinalityProofRequestBuilder<B>>,
	/// Fork sync targets.
	fork_targets: HashMap<B::Hash, ForkTarget<B>>,
	/// A set of peers for which there might be potential block requests
	pending_requests: PendingRequests,
	/// A type to check incoming block announcements.
	block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,
	/// Maximum number of peers to ask the same blocks in parallel.
	max_parallel_downloads: u32,
	/// Total number of processed blocks (imported or failed).
	processed_blocks: usize,
}

/// All the data we have about a Peer that we are trying to sync with
#[derive(Debug, Clone)]
pub struct PeerSync<B: BlockT> {
	/// The common number is the block number that is a common point of
	/// ancestry for both our chains (as far as we know).
	pub common_number: NumberFor<B>,
	/// The hash of the best block that we've seen for this peer.
	pub best_hash: B::Hash,
	/// The number of the best block that we've seen for this peer.
	pub best_number: NumberFor<B>,
	/// The state of syncing this peer is in for us, generally categories
	/// into `Available` or "busy" with something as defined by `PeerSyncState`.
	pub state: PeerSyncState<B>,
	/// A queue of blocks that this peer has announced to us, should only
	/// contain `ANNOUNCE_HISTORY_SIZE` entries.
	pub recently_announced: VecDeque<B::Hash>
}

/// The sync status of a peer we are trying to sync with
#[derive(Debug)]
pub struct PeerInfo<B: BlockT> {
	/// Their best block hash.
	pub best_hash: B::Hash,
	/// Their best block number.
	pub best_number: NumberFor<B>
}

struct ForkTarget<B: BlockT> {
	number: NumberFor<B>,
	parent_hash: Option<B::Hash>,
	peers: HashSet<PeerId>,
}

/// The state of syncing between a Peer and ourselves.
///
/// Generally two categories, "busy" or `Available`. If busy, the enum
/// defines what we are busy with.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum PeerSyncState<B: BlockT> {
	/// Available for sync requests.
	Available,
	/// Searching for ancestors the Peer has in common with us.
	AncestorSearch {
		start: NumberFor<B>,
		current: NumberFor<B>,
		state: AncestorSearchState<B>,
	},
	/// Actively downloading new blocks, starting from the given Number.
	DownloadingNew(NumberFor<B>),
	/// Downloading a stale block with given Hash. Stale means that it is a
	/// block with a number that is lower than our best number. It might be
	/// from a fork and not necessarily already imported.
	DownloadingStale(B::Hash),
	/// Downloading justification for given block hash.
	DownloadingJustification(B::Hash),
	/// Downloading finality proof for given block hash.
	DownloadingFinalityProof(B::Hash)
}

impl<B: BlockT> PeerSyncState<B> {
	pub fn is_available(&self) -> bool {
		if let PeerSyncState::Available = self {
			true
		} else {
			false
		}
	}
}

/// Reported sync state.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum SyncState {
	/// Initial sync is complete, keep-up sync is active.
	Idle,
	/// Actively catching up with the chain.
	Downloading
}

/// Syncing status and statistics.
#[derive(Clone)]
pub struct Status<B: BlockT> {
	/// Current global sync state.
	pub state: SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<NumberFor<B>>,
	/// Number of peers participating in syncing.
	pub num_peers: u32,
	/// Number of blocks queued for import
	pub queued_blocks: u32,
}

/// A peer did not behave as expected and should be reported.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BadPeer(pub PeerId, pub sc_peerset::ReputationChange);

impl fmt::Display for BadPeer {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
		write!(f, "Bad peer {}; Reputation change: {:?}", self.0, self.1)
	}
}

impl std::error::Error for BadPeer {}

/// Result of [`ChainSync::on_block_data`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OnBlockData<B: BlockT> {
	/// The block should be imported.
	Import(BlockOrigin, Vec<IncomingBlock<B>>),
	/// A new block request needs to be made to the given peer.
	Request(PeerId, BlockRequest<B>)
}

/// Result of [`ChainSync::on_block_announce`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OnBlockAnnounce {
	/// The announcement does not require further handling.
	Nothing,
	/// The announcement header should be imported.
	ImportHeader,
}

/// Result of [`ChainSync::on_block_justification`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OnBlockJustification<B: BlockT> {
	/// The justification needs no further handling.
	Nothing,
	/// The justification should be imported.
	Import {
		peer: PeerId,
		hash: B::Hash,
		number: NumberFor<B>,
		justification: Justification
	}
}

/// Result of [`ChainSync::on_block_finality_proof`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum OnBlockFinalityProof<B: BlockT> {
	/// The proof needs no further handling.
	Nothing,
	/// The proof should be imported.
	Import {
		peer: PeerId,
		hash: B::Hash,
		number: NumberFor<B>,
		proof: Vec<u8>
	}
}

impl<B: BlockT> ChainSync<B> {
	/// Create a new instance.
	pub fn new(
		role: Roles,
		client: Arc<dyn crate::chain::Client<B>>,
		info: &BlockchainInfo<B>,
		request_builder: Option<BoxFinalityProofRequestBuilder<B>>,
		block_announce_validator: Box<dyn BlockAnnounceValidator<B> + Send>,
		max_parallel_downloads: u32,
	) -> Self {
		let mut required_block_attributes = BlockAttributes::HEADER | BlockAttributes::JUSTIFICATION;

		if role.is_full() {
			required_block_attributes |= BlockAttributes::BODY
		}

		ChainSync {
			client,
			peers: HashMap::new(),
			blocks: BlockCollection::new(),
			best_queued_hash: info.best_hash,
			best_queued_number: info.best_number,
			best_imported_number: info.best_number,
			extra_finality_proofs: ExtraRequests::new("finality proof"),
			extra_justifications: ExtraRequests::new("justification"),
			role,
			required_block_attributes,
			queue_blocks: Default::default(),
			request_builder,
			fork_targets: Default::default(),
			pending_requests: Default::default(),
			block_announce_validator,
			max_parallel_downloads,
			processed_blocks: 0,
		}
	}

	/// Returns the state of the sync of the given peer.
	///
	/// Returns `None` if the peer is unknown.
	pub fn peer_info(&self, who: &PeerId) -> Option<PeerInfo<B>> {
		self.peers.get(who).map(|p| PeerInfo { best_hash: p.best_hash, best_number: p.best_number })
	}

	/// Returns the current sync status.
	pub fn status(&self) -> Status<B> {
		let best_seen = self.peers.values().max_by_key(|p| p.best_number).map(|p| p.best_number);
		let sync_state =
			if let Some(n) = best_seen {
				// A chain is classified as downloading if the provided best block is
				// more than `MAJOR_SYNC_BLOCKS` behind the best queued block.
				if n > self.best_queued_number && n - self.best_queued_number > MAJOR_SYNC_BLOCKS.into() {
					SyncState::Downloading
				} else {
					SyncState::Idle
				}
			} else {
				SyncState::Idle
			};

		Status {
			state: sync_state,
			best_seen_block: best_seen,
			num_peers: self.peers.len() as u32,
			queued_blocks: self.queue_blocks.len() as u32,
		}
	}

	/// Number of active sync requests.
	pub fn num_sync_requests(&self) -> usize {
		self.fork_targets.len()
	}

	/// Number of processed blocks.
	pub fn num_processed_blocks(&self) -> usize {
		self.processed_blocks
	}

	/// Handle a new connected peer.
	///
	/// Call this method whenever we connect to a new peer.
	pub fn new_peer(&mut self, who: PeerId, best_hash: B::Hash, best_number: NumberFor<B>)
		-> Result<Option<BlockRequest<B>>, BadPeer>
	{
		// There is nothing sync can get from the node that has no blockchain data.
		match self.block_status(&best_hash) {
			Err(e) => {
				debug!(target:"sync", "Error reading blockchain: {:?}", e);
				Err(BadPeer(who, rep::BLOCKCHAIN_READ_ERROR))
			}
			Ok(BlockStatus::KnownBad) => {
				info!("💔 New peer with known bad best block {} ({}).", best_hash, best_number);
				Err(BadPeer(who, rep::BAD_BLOCK))
			}
			Ok(BlockStatus::Unknown) => {
				if best_number.is_zero() {
					info!("💔 New peer with unknown genesis hash {} ({}).", best_hash, best_number);
					return Err(BadPeer(who, rep::GENESIS_MISMATCH));
				}
				// If there are more than `MAJOR_SYNC_BLOCKS` in the import queue then we have
				// enough to do in the import queue that it's not worth kicking off
				// an ancestor search, which is what we do in the next match case below.
				if self.queue_blocks.len() > MAJOR_SYNC_BLOCKS.into() {
					debug!(
						target:"sync",
						"New peer with unknown best hash {} ({}), assuming common block.",
						self.best_queued_hash,
						self.best_queued_number
					);
					self.peers.insert(who, PeerSync {
						common_number: self.best_queued_number,
						best_hash,
						best_number,
						state: PeerSyncState::Available,
						recently_announced: Default::default()
					});
					return Ok(None)
				}

				// If we are at genesis, just start downloading.
				if self.best_queued_number.is_zero() {
					debug!(target:"sync", "New peer with best hash {} ({}).", best_hash, best_number);
					self.peers.insert(who.clone(), PeerSync {
						common_number: Zero::zero(),
						best_hash,
						best_number,
						state: PeerSyncState::Available,
						recently_announced: Default::default(),
					});
					self.pending_requests.add(&who);
					return Ok(None)
				}

				let common_best = std::cmp::min(self.best_queued_number, best_number);

				debug!(target:"sync",
					"New peer with unknown best hash {} ({}), searching for common ancestor.",
					best_hash,
					best_number
				);

				self.pending_requests.add(&who);
				self.peers.insert(who, PeerSync {
					common_number: Zero::zero(),
					best_hash,
					best_number,
					state: PeerSyncState::AncestorSearch {
						current: common_best,
						start: self.best_queued_number,
						state: AncestorSearchState::ExponentialBackoff(One::one()),
					},
					recently_announced: Default::default()
				});

				Ok(Some(ancestry_request::<B>(common_best)))
			}
			Ok(BlockStatus::Queued) | Ok(BlockStatus::InChainWithState) | Ok(BlockStatus::InChainPruned) => {
				debug!(target:"sync", "New peer with known best hash {} ({}).", best_hash, best_number);
				self.peers.insert(who.clone(), PeerSync {
					common_number: best_number,
					best_hash,
					best_number,
					state: PeerSyncState::Available,
					recently_announced: Default::default(),
				});
				self.pending_requests.add(&who);
				Ok(None)
			}
		}
	}

	/// Signal that `best_header` has been queued for import and update the
	/// `ChainSync` state with that information.
	pub fn update_chain_info(&mut self, best_header: &B::Header) {
		self.on_block_queued(&best_header.hash(), *best_header.number())
	}

	/// Schedule a justification request for the given block.
	pub fn request_justification(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let client = &self.client;
		self.extra_justifications.schedule((*hash, number), |base, block| {
			is_descendent_of(&**client, base, block)
		})
	}

	/// Schedule a finality proof request for the given block.
	pub fn request_finality_proof(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let client = &self.client;
		self.extra_finality_proofs.schedule((*hash, number), |base, block| {
			is_descendent_of(&**client, base, block)
		})
	}

	/// Request syncing for the given block from given set of peers.
	// The implementation is similar to on_block_announce with unknown parent hash.
	pub fn set_sync_fork_request(
		&mut self,
		mut peers: Vec<PeerId>,
		hash: &B::Hash,
		number: NumberFor<B>,
	) {
		if peers.is_empty() {
			peers = self.peers.iter()
				// Only request blocks from peers who are ahead or on a par.
				.filter(|(_, peer)| peer.best_number >= number)
				.map(|(id, _)| id.clone())
				.collect();

			debug!(
				target: "sync",
				"Explicit sync request for block {:?} with no peers specified. \
				Syncing from these peers {:?} instead.",
				hash, peers,
			);
		} else {
			debug!(target: "sync", "Explicit sync request for block {:?} with {:?}", hash, peers);
		}

		if self.is_known(&hash) {
			debug!(target: "sync", "Refusing to sync known hash {:?}", hash);
			return;
		}

		trace!(target: "sync", "Downloading requested old fork {:?}", hash);
		for peer_id in &peers {
			if let Some(peer) = self.peers.get_mut(peer_id) {
				if let PeerSyncState::AncestorSearch {..} = peer.state {
					continue;
				}

				if number > peer.best_number {
					peer.best_number = number;
					peer.best_hash = hash.clone();
				}
				self.pending_requests.add(peer_id);
			}
		}

		self.fork_targets
			.entry(hash.clone())
			.or_insert_with(|| ForkTarget {
				number,
				peers: Default::default(),
				parent_hash: None,
			})
			.peers.extend(peers);
	}

	/// Get an iterator over all scheduled justification requests.
	pub fn justification_requests(&mut self) -> impl Iterator<Item = (PeerId, BlockRequest<B>)> + '_ {
		let peers = &mut self.peers;
		let mut matcher = self.extra_justifications.matcher();
		std::iter::from_fn(move || {
			if let Some((peer, request)) = matcher.next(&peers) {
				peers.get_mut(&peer)
					.expect("`Matcher::next` guarantees the `PeerId` comes from the given peers; qed")
					.state = PeerSyncState::DownloadingJustification(request.0);
				let req = message::generic::BlockRequest {
					id: 0,
					fields: BlockAttributes::JUSTIFICATION,
					from: message::FromBlock::Hash(request.0),
					to: None,
					direction: message::Direction::Ascending,
					max: Some(1)
				};
				Some((peer, req))
			} else {
				None
			}
		})
	}

	/// Get an iterator over all scheduled finality proof requests.
	pub fn finality_proof_requests(&mut self) -> impl Iterator<Item = (PeerId, FinalityProofRequest<B::Hash>)> + '_ {
		let peers = &mut self.peers;
		let request_builder = &mut self.request_builder;
		let mut matcher = self.extra_finality_proofs.matcher();
		std::iter::from_fn(move || {
			if let Some((peer, request)) = matcher.next(&peers) {
				peers.get_mut(&peer)
					.expect("`Matcher::next` guarantees the `PeerId` comes from the given peers; qed")
					.state = PeerSyncState::DownloadingFinalityProof(request.0);
				let req = message::generic::FinalityProofRequest {
					id: 0,
					block: request.0,
					request: request_builder.as_mut()
						.map(|builder| builder.build_request_data(&request.0))
						.unwrap_or_default()
				};
				Some((peer, req))
			} else {
				None
			}
		})
	}

	/// Get an iterator over all block requests of all peers.
	pub fn block_requests(&mut self) -> impl Iterator<Item = (PeerId, BlockRequest<B>)> + '_ {
		if self.pending_requests.is_empty() {
			return Either::Left(std::iter::empty())
		}
		if self.queue_blocks.len() > MAX_IMPORTING_BLOCKS {
			trace!(target: "sync", "Too many blocks in the queue.");
			return Either::Left(std::iter::empty())
		}
		let major_sync = self.status().state == SyncState::Downloading;
		let blocks = &mut self.blocks;
		let attrs = &self.required_block_attributes;
		let fork_targets = &mut self.fork_targets;
		let mut have_requests = false;
		let last_finalized = self.client.info().finalized_number;
		let best_queued = self.best_queued_number;
		let client = &self.client;
		let queue = &self.queue_blocks;
		let pending_requests = self.pending_requests.take();
		let max_parallel = if major_sync { 1 } else { self.max_parallel_downloads };
		let iter = self.peers.iter_mut().filter_map(move |(id, peer)| {
			if !peer.state.is_available() || !pending_requests.contains(id) {
				return None
			}

			if let Some((range, req)) = peer_block_request(
				id,
				peer,
				blocks,
				attrs,
				max_parallel,
				last_finalized,
				best_queued,
			) {
				peer.state = PeerSyncState::DownloadingNew(range.start);
				trace!(
					target: "sync",
					"New block request for {}, (best:{}, common:{}) {:?}",
					id,
					peer.best_number,
					peer.common_number,
					req,
				);
				have_requests = true;
				Some((id.clone(), req))
			} else if let Some((hash, req)) = fork_sync_request(
				id,
				fork_targets,
				best_queued,
				last_finalized,
				attrs,
				|hash| if queue.contains(hash) {
					BlockStatus::Queued
				} else {
					client.block_status(&BlockId::Hash(*hash)).unwrap_or(BlockStatus::Unknown)
				},
			) {
				trace!(target: "sync", "Downloading fork {:?} from {}", hash, id);
				peer.state = PeerSyncState::DownloadingStale(hash);
				have_requests = true;
				Some((id.clone(), req))
			} else {
				None
			}
		});
		Either::Right(iter)
	}

	/// Handle a response from the remote to a block request that we made.
	///
	/// `request` must be the original request that triggered `response`.
	/// or `None` if data comes from the block announcement.
	///
	/// If this corresponds to a valid block, this outputs the block that
	/// must be imported in the import queue.
	pub fn on_block_data
		(&mut self, who: PeerId, request: Option<BlockRequest<B>>, response: BlockResponse<B>) -> Result<OnBlockData<B>, BadPeer>
	{
		let mut new_blocks: Vec<IncomingBlock<B>> =
			if let Some(peer) = self.peers.get_mut(&who) {
				let mut blocks = response.blocks;
				if request.as_ref().map_or(false, |r| r.direction == message::Direction::Descending) {
					trace!(target: "sync", "Reversing incoming block list");
					blocks.reverse()
				}
				self.pending_requests.add(&who);
				if request.is_some() {
					match &mut peer.state {
						PeerSyncState::DownloadingNew(start_block) => {
							self.blocks.clear_peer_download(&who);
							let start_block = *start_block;
							peer.state = PeerSyncState::Available;
							validate_blocks::<B>(&blocks, &who)?;
							self.blocks.insert(start_block, blocks, who.clone());
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
										allow_missing_state: true,
										import_existing: false,
									}
								}).collect()
						}
						PeerSyncState::DownloadingStale(_) => {
							peer.state = PeerSyncState::Available;
							if blocks.is_empty() {
								debug!(target: "sync", "Empty block response from {}", who);
								return Err(BadPeer(who, rep::NO_BLOCK));
							}
							validate_blocks::<B>(&blocks, &who)?;
							blocks.into_iter().map(|b| {
								IncomingBlock {
									hash: b.hash,
									header: b.header,
									body: b.body,
									justification: b.justification,
									origin: Some(who.clone()),
									allow_missing_state: true,
									import_existing: false,
								}
							}).collect()
						}
						PeerSyncState::AncestorSearch { current, start, state } => {
							let matching_hash = match (blocks.get(0), self.client.hash(*current)) {
								(Some(block), Ok(maybe_our_block_hash)) => {
									trace!(target: "sync", "Got ancestry block #{} ({}) from peer {}", current, block.hash, who);
									maybe_our_block_hash.filter(|x| x == &block.hash)
								},
								(None, _) => {
									debug!(target: "sync", "Invalid response when searching for ancestor from {}", who);
									return Err(BadPeer(who, rep::UNKNOWN_ANCESTOR))
								},
								(_, Err(e)) => {
									info!("❌ Error answering legitimate blockchain query: {:?}", e);
									return Err(BadPeer(who, rep::BLOCKCHAIN_READ_ERROR))
								}
							};
							if matching_hash.is_some() {
								if *start < self.best_queued_number && self.best_queued_number <= peer.best_number {
									// We've made progress on this chain since the search was started.
									// Opportunistically set common number to updated number
									// instead of the one that started the search.
									peer.common_number = self.best_queued_number;
								}
								else if peer.common_number < *current {
									peer.common_number = *current;
								}
							}
							if matching_hash.is_none() && current.is_zero() {
								trace!(target:"sync", "Ancestry search: genesis mismatch for peer {}", who);
								return Err(BadPeer(who, rep::GENESIS_MISMATCH))
							}
							if let Some((next_state, next_num)) = handle_ancestor_search_state(state, *current, matching_hash.is_some()) {
								peer.state = PeerSyncState::AncestorSearch {
									current: next_num,
									start: *start,
									state: next_state,
								};
								return Ok(OnBlockData::Request(who, ancestry_request::<B>(next_num)))
							} else {
								// Ancestry search is complete. Check if peer is on a stale fork unknown to us and
								// add it to sync targets if necessary.
								trace!(target: "sync", "Ancestry search complete. Ours={} ({}), Theirs={} ({}), Common={:?} ({})",
									self.best_queued_hash,
									self.best_queued_number,
									peer.best_hash,
									peer.best_number,
									matching_hash,
									peer.common_number,
								);
								if peer.common_number < peer.best_number
									&& peer.best_number < self.best_queued_number
								{
									trace!(target: "sync", "Added fork target {} for {}" , peer.best_hash, who);
									self.fork_targets
										.entry(peer.best_hash.clone())
										.or_insert_with(|| ForkTarget {
											number: peer.best_number,
											parent_hash: None,
											peers: Default::default(),
										})
									.peers.insert(who.clone());
								}
								peer.state = PeerSyncState::Available;
								Vec::new()
							}
						}

						| PeerSyncState::Available
						| PeerSyncState::DownloadingJustification(..)
						| PeerSyncState::DownloadingFinalityProof(..) => Vec::new()
					}
				} else {
					// When request.is_none() this is a block announcement. Just accept blocks.
					validate_blocks::<B>(&blocks, &who)?;
					blocks.into_iter().map(|b| {
						IncomingBlock {
							hash: b.hash,
							header: b.header,
							body: b.body,
							justification: b.justification,
							origin: Some(who.clone()),
							allow_missing_state: true,
							import_existing: false,
						}
					}).collect()
				}
			} else {
				Vec::new()
			};

		// When doing initial sync we don't request blocks in parallel.
		// So the only way this can happen is when peers lie about the
		// common block.
		let is_recent = new_blocks.first()
			.map(|block| {
				self.peers.iter().any(|(_, peer)| peer.recently_announced.contains(&block.hash))
			})
			.unwrap_or(false);

		if !is_recent && new_blocks.last().map_or(false, |b| self.is_known(&b.hash)) {
			// When doing initial sync we don't request blocks in parallel.
			// So the only way this can happen is when peers lie about the
			// common block.
			debug!(target: "sync", "Ignoring known blocks from {}", who);
			return Err(BadPeer(who, rep::KNOWN_BLOCK));
		}
		let orig_len = new_blocks.len();
		new_blocks.retain(|b| !self.queue_blocks.contains(&b.hash));
		if new_blocks.len() != orig_len {
			debug!(target: "sync", "Ignoring {} blocks that are already queued", orig_len - new_blocks.len());
		}

		let origin =
			if is_recent {
				BlockOrigin::NetworkBroadcast
			} else {
				BlockOrigin::NetworkInitialSync
			};

		if let Some((h, n)) = new_blocks.last().and_then(|b| b.header.as_ref().map(|h| (&b.hash, *h.number()))) {
			trace!(target:"sync", "Accepted {} blocks ({:?}) with origin {:?}", new_blocks.len(), h, origin);
			self.on_block_queued(h, n)
		}

		self.queue_blocks.extend(new_blocks.iter().map(|b| b.hash));

		Ok(OnBlockData::Import(origin, new_blocks))
	}

	/// Handle a response from the remote to a justification request that we made.
	///
	/// `request` must be the original request that triggered `response`.
	///
	/// Returns `Some` if this produces a justification that must be imported
	/// into the import queue.
	pub fn on_block_justification
		(&mut self, who: PeerId, response: BlockResponse<B>) -> Result<OnBlockJustification<B>, BadPeer>
	{
		let peer =
			if let Some(peer) = self.peers.get_mut(&who) {
				peer
			} else {
				error!(target: "sync", "💔 Called on_block_justification with a bad peer ID");
				return Ok(OnBlockJustification::Nothing)
			};

		self.pending_requests.add(&who);
		if let PeerSyncState::DownloadingJustification(hash) = peer.state {
			peer.state = PeerSyncState::Available;

			// We only request one justification at a time
			let justification = if let Some(block) = response.blocks.into_iter().next() {
				if hash != block.hash {
					info!(
						target: "sync",
						"💔 Invalid block justification provided by {}: requested: {:?} got: {:?}", who, hash, block.hash
					);
					return Err(BadPeer(who, rep::BAD_JUSTIFICATION));
				}

				block.justification
			} else {
				// we might have asked the peer for a justification on a block that we assumed it
				// had but didn't (regardless of whether it had a justification for it or not).
				trace!(target: "sync",
					"Peer {:?} provided empty response for justification request {:?}",
					who,
					hash,
				);

				None
			};

			if let Some((peer, hash, number, j)) = self.extra_justifications.on_response(who, justification) {
				return Ok(OnBlockJustification::Import { peer, hash, number, justification: j })
			}
		}

		Ok(OnBlockJustification::Nothing)
	}

	/// Handle new finality proof data.
	pub fn on_block_finality_proof
		(&mut self, who: PeerId, resp: FinalityProofResponse<B::Hash>) -> Result<OnBlockFinalityProof<B>, BadPeer>
	{
		let peer =
			if let Some(peer) = self.peers.get_mut(&who) {
				peer
			} else {
				error!(target: "sync", "💔 Called on_block_finality_proof_data with a bad peer ID");
				return Ok(OnBlockFinalityProof::Nothing)
			};

		self.pending_requests.add(&who);
		if let PeerSyncState::DownloadingFinalityProof(hash) = peer.state {
			peer.state = PeerSyncState::Available;

			// We only request one finality proof at a time.
			if hash != resp.block {
				info!(
					target: "sync",
					"💔 Invalid block finality proof provided: requested: {:?} got: {:?}",
					hash,
					resp.block
				);
				return Err(BadPeer(who, rep::BAD_FINALITY_PROOF));
			}

			if let Some((peer, hash, number, p)) = self.extra_finality_proofs.on_response(who, resp.proof) {
				return Ok(OnBlockFinalityProof::Import { peer, hash, number, proof: p })
			}
		}

		Ok(OnBlockFinalityProof::Nothing)
	}

	/// A batch of blocks have been processed, with or without errors.
	///
	/// Call this when a batch of blocks have been processed by the import
	/// queue, with or without errors.
	///
	/// `peer_info` is passed in case of a restart.
	pub fn on_blocks_processed<'a>(
		&'a mut self,
		imported: usize,
		count: usize,
		results: Vec<(Result<BlockImportResult<NumberFor<B>>, BlockImportError>, B::Hash)>,
	) -> impl Iterator<Item = Result<(PeerId, BlockRequest<B>), BadPeer>> + 'a {
		trace!(target: "sync", "Imported {} of {}", imported, count);

		let mut output = Vec::new();

		let mut has_error = false;
		for (_, hash) in &results {
			self.queue_blocks.remove(&hash);
		}
		self.processed_blocks += results.len();

		for (result, hash) in results {
			if has_error {
				continue;
			}

			if result.is_err() {
				has_error = true;
			}

			match result {
				Ok(BlockImportResult::ImportedKnown(_number)) => {}
				Ok(BlockImportResult::ImportedUnknown(number, aux, who)) => {
					if aux.clear_justification_requests {
						trace!(
							target: "sync",
							"Block imported clears all pending justification requests {}: {:?}",
							number,
							hash
						);
						self.extra_justifications.reset()
					}

					if aux.needs_justification {
						trace!(target: "sync", "Block imported but requires justification {}: {:?}", number, hash);
						self.request_justification(&hash, number);
					}

					if aux.bad_justification {
						if let Some(peer) = who {
							info!("💔 Sent block with bad justification to import");
							output.push(Err(BadPeer(peer, rep::BAD_JUSTIFICATION)));
						}
					}

					if aux.needs_finality_proof {
						trace!(target: "sync", "Block imported but requires finality proof {}: {:?}", number, hash);
						self.request_finality_proof(&hash, number);
					}

					if number > self.best_imported_number {
						self.best_imported_number = number;
					}
				},
				Err(BlockImportError::IncompleteHeader(who)) => {
					if let Some(peer) = who {
						warn!("💔 Peer sent block with incomplete header to import");
						output.push(Err(BadPeer(peer, rep::INCOMPLETE_HEADER)));
						output.extend(self.restart());
					}
				},
				Err(BlockImportError::VerificationFailed(who, e)) => {
					if let Some(peer) = who {
						warn!("💔 Verification failed for block {:?} received from peer: {}, {:?}", hash, peer, e);
						output.push(Err(BadPeer(peer, rep::VERIFICATION_FAIL)));
						output.extend(self.restart());
					}
				},
				Err(BlockImportError::BadBlock(who)) => {
					if let Some(peer) = who {
						info!("💔 Block {:?} received from peer {} has been blacklisted", hash, peer);
						output.push(Err(BadPeer(peer, rep::BAD_BLOCK)));
					}
				},
				Err(BlockImportError::MissingState) => {
					// This may happen if the chain we were requesting upon has been discarded
					// in the meantime because other chain has been finalized.
					// Don't mark it as bad as it still may be synced if explicitly requested.
					trace!(target: "sync", "Obsolete block {:?}", hash);
				},
				e @ Err(BlockImportError::UnknownParent) |
				e @ Err(BlockImportError::Other(_)) => {
					warn!(target: "sync", "💔 Error importing block {:?}: {:?}", hash, e);
					output.extend(self.restart());
				},
				Err(BlockImportError::Cancelled) => {}
			};
		}

		self.pending_requests.set_all();
		output.into_iter()
	}

	/// Call this when a justification has been processed by the import queue,
	/// with or without errors.
	pub fn on_justification_import(&mut self, hash: B::Hash, number: NumberFor<B>, success: bool) {
		let finalization_result = if success { Ok((hash, number)) } else { Err(()) };
		self.extra_justifications.try_finalize_root((hash, number), finalization_result, true);
		self.pending_requests.set_all();
	}

	pub fn on_finality_proof_import(&mut self, req: (B::Hash, NumberFor<B>), res: Result<(B::Hash, NumberFor<B>), ()>) {
		self.extra_finality_proofs.try_finalize_root(req, res, true);
		self.pending_requests.set_all();
	}

	/// Notify about finalization of the given block.
	pub fn on_block_finalized(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		let client = &self.client;
		let r = self.extra_finality_proofs.on_block_finalized(hash, number, |base, block| {
			is_descendent_of(&**client, base, block)
		});

		if let Err(err) = r {
			warn!(target: "sync", "💔 Error cleaning up pending extra finality proof data requests: {:?}", err)
		}

		let client = &self.client;
		let r = self.extra_justifications.on_block_finalized(hash, number, |base, block| {
			is_descendent_of(&**client, base, block)
		});

		if let Err(err) = r {
			warn!(target: "sync", "💔 Error cleaning up pending extra justification data requests: {:?}", err);
		}
	}

	/// Called when a block has been queued for import.
	///
	/// Updates our internal state for best queued block and then goes
	/// through all peers to update our view of their state as well.
	fn on_block_queued(&mut self, hash: &B::Hash, number: NumberFor<B>) {
		if let Some(_) = self.fork_targets.remove(&hash) {
			trace!(target: "sync", "Completed fork sync {:?}", hash);
		}
		if number > self.best_queued_number {
			self.best_queued_number = number;
			self.best_queued_hash = *hash;
			// Update common blocks
			for (n, peer) in self.peers.iter_mut() {
				if let PeerSyncState::AncestorSearch {..} = peer.state {
					// Wait for ancestry search to complete first.
					continue;
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
		self.pending_requests.set_all();
	}

	/// Call when a node announces a new block.
	///
	/// If `OnBlockAnnounce::ImportHeader` is returned, then the caller MUST try to import passed
	/// header (call `on_block_data`). The network request isn't sent
	/// in this case. Both hash and header is passed as an optimization
	/// to avoid rehashing the header.
	pub fn on_block_announce(&mut self, who: PeerId, hash: B::Hash, announce: &BlockAnnounce<B::Header>, is_best: bool)
		-> OnBlockAnnounce
	{
		let header = &announce.header;
		let number = *header.number();
		debug!(target: "sync", "Received block announcement {:?} with number {:?} from {}", hash, number, who);
		if number.is_zero() {
			warn!(target: "sync", "💔 Ignored genesis block (#0) announcement from {}: {}", who, hash);
			return OnBlockAnnounce::Nothing
		}
		let parent_status = self.block_status(header.parent_hash()).ok().unwrap_or(BlockStatus::Unknown);
		let known_parent = parent_status != BlockStatus::Unknown;
		let ancient_parent = parent_status == BlockStatus::InChainPruned;

		let known = self.is_known(&hash);
		let peer = if let Some(peer) = self.peers.get_mut(&who) {
			peer
		} else {
			error!(target: "sync", "💔 Called on_block_announce with a bad peer ID");
			return OnBlockAnnounce::Nothing
		};
		while peer.recently_announced.len() >= ANNOUNCE_HISTORY_SIZE {
			peer.recently_announced.pop_front();
		}
		peer.recently_announced.push_back(hash.clone());
		if is_best {
			// update their best block
			peer.best_number = number;
			peer.best_hash = hash;
		}
		if let PeerSyncState::AncestorSearch {..} = peer.state {
			return OnBlockAnnounce::Nothing
		}
		// If the announced block is the best they have and is not ahead of us, our common number
		// is either one further ahead or it's the one they just announced, if we know about it.
		if is_best {
			if known && self.best_queued_number >= number {
				peer.common_number = number
			} else if header.parent_hash() == &self.best_queued_hash
				|| known_parent && self.best_queued_number >= number
			{
				peer.common_number = number - One::one();
			}
		}
		self.pending_requests.add(&who);

		// known block case
		if known || self.is_already_downloading(&hash) {
			trace!(target: "sync", "Known block announce from {}: {}", who, hash);
			if let Some(target) = self.fork_targets.get_mut(&hash) {
				target.peers.insert(who);
			}
			return OnBlockAnnounce::Nothing
		}

		// Let external validator check the block announcement.
		let assoc_data = announce.data.as_ref().map_or(&[][..], |v| v.as_slice());
		match self.block_announce_validator.validate(&header, assoc_data) {
			Ok(Validation::Success) => (),
			Ok(Validation::Failure) => {
				debug!(target: "sync", "Block announcement validation of block {} from {} failed", hash, who);
				return OnBlockAnnounce::Nothing
			}
			Err(e) => {
				error!(target: "sync", "💔 Block announcement validation errored: {}", e);
				return OnBlockAnnounce::Nothing
			}
		}

		if ancient_parent {
			trace!(target: "sync", "Ignored ancient block announced from {}: {} {:?}", who, hash, header);
			return OnBlockAnnounce::Nothing
		}

		let requires_additional_data = !self.role.is_light() || !known_parent;
		if !requires_additional_data {
			trace!(target: "sync", "Importing new header announced from {}: {} {:?}", who, hash, header);
			return OnBlockAnnounce::ImportHeader
		}

		if number <= self.best_queued_number {
			trace!(
				target: "sync",
				"Added sync target for block announced from {}: {} {:?}", who, hash, header
			);
			self.fork_targets
				.entry(hash.clone())
				.or_insert_with(|| ForkTarget {
					number,
					parent_hash: Some(header.parent_hash().clone()),
					peers: Default::default(),
				})
				.peers.insert(who);
		}

		OnBlockAnnounce::Nothing
	}

	/// Call when a peer has disconnected.
	pub fn peer_disconnected(&mut self, who: PeerId) {
		self.blocks.clear_peer_download(&who);
		self.peers.remove(&who);
		self.extra_justifications.peer_disconnected(&who);
		self.extra_finality_proofs.peer_disconnected(&who);
		self.pending_requests.set_all();
	}

	/// Restart the sync process.
	fn restart<'a>(&'a mut self) -> impl Iterator<Item = Result<(PeerId, BlockRequest<B>), BadPeer>> + 'a {
		self.processed_blocks = 0;
		self.blocks.clear();
		let info = self.client.info();
		self.best_queued_hash = info.best_hash;
		self.best_queued_number = std::cmp::max(info.best_number, self.best_imported_number);
		self.pending_requests.set_all();
		debug!(target:"sync", "Restarted with {} ({})", self.best_queued_number, self.best_queued_hash);
		let old_peers = std::mem::take(&mut self.peers);
		old_peers.into_iter().filter_map(move |(id, p)| {
			match self.new_peer(id.clone(), p.best_hash, p.best_number) {
				Ok(None) => None,
				Ok(Some(x)) => Some(Ok((id, x))),
				Err(e) => Some(Err(e))
			}
		})
	}

	/// What is the status of the block corresponding to the given hash?
	fn block_status(&self, hash: &B::Hash) -> Result<BlockStatus, ClientError> {
		if self.queue_blocks.contains(hash) {
			return Ok(BlockStatus::Queued)
		}
		self.client.block_status(&BlockId::Hash(*hash))
	}

	/// Is the block corresponding to the given hash known?
	fn is_known(&self, hash: &B::Hash) -> bool {
		self.block_status(hash).ok().map_or(false, |s| s != BlockStatus::Unknown)
	}

	/// Is any peer downloading the given hash?
	fn is_already_downloading(&self, hash: &B::Hash) -> bool {
		self.peers.iter().any(|(_, p)| p.state == PeerSyncState::DownloadingStale(*hash))
	}

	/// Return some key metrics.
	pub(crate) fn metrics(&self) -> Metrics {
		use std::convert::TryInto;
		Metrics {
			queued_blocks: self.queue_blocks.len().try_into().unwrap_or(std::u32::MAX),
			fork_targets: self.fork_targets.len().try_into().unwrap_or(std::u32::MAX),
			finality_proofs: self.extra_finality_proofs.metrics(),
			justifications: self.extra_justifications.metrics(),
			_priv: ()
		}
	}
}

#[derive(Debug)]
pub(crate) struct Metrics {
	pub(crate) queued_blocks: u32,
	pub(crate) fork_targets: u32,
	pub(crate) finality_proofs: extra_requests::Metrics,
	pub(crate) justifications: extra_requests::Metrics,
	_priv: ()
}

/// Request the ancestry for a block. Sends a request for header and justification for the given
/// block number. Used during ancestry search.
fn ancestry_request<B: BlockT>(block: NumberFor<B>) -> BlockRequest<B> {
	message::generic::BlockRequest {
		id: 0,
		fields: BlockAttributes::HEADER | BlockAttributes::JUSTIFICATION,
		from: message::FromBlock::Number(block),
		to: None,
		direction: message::Direction::Ascending,
		max: Some(1)
	}
}

/// The ancestor search state expresses which algorithm, and its stateful parameters, we are using to
/// try to find an ancestor block
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum AncestorSearchState<B: BlockT> {
	/// Use exponential backoff to find an ancestor, then switch to binary search.
	/// We keep track of the exponent.
	ExponentialBackoff(NumberFor<B>),
	/// Using binary search to find the best ancestor.
	/// We keep track of left and right bounds.
	BinarySearch(NumberFor<B>, NumberFor<B>),
}

/// This function handles the ancestor search strategy used. The goal is to find a common point
/// that both our chains agree on that is as close to the tip as possible.
/// The way this works is we first have an exponential backoff strategy, where we try to step
/// forward until we find a block hash mismatch. The size of the step doubles each step we take.
///
/// When we've found a block hash mismatch we then fall back to a binary search between the two
/// last known points to find the common block closest to the tip.
fn handle_ancestor_search_state<B: BlockT>(
	state: &AncestorSearchState<B>,
	curr_block_num: NumberFor<B>,
	block_hash_match: bool
) -> Option<(AncestorSearchState<B>, NumberFor<B>)> {
	let two = <NumberFor<B>>::one() + <NumberFor<B>>::one();
	match state {
		AncestorSearchState::ExponentialBackoff(next_distance_to_tip) => {
			let next_distance_to_tip = *next_distance_to_tip;
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
		}
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
		}
	}
}

/// Get a new block request for the peer if any.
fn peer_block_request<B: BlockT>(
	id: &PeerId,
	peer: &PeerSync<B>,
	blocks: &mut BlockCollection<B>,
	attrs: &message::BlockAttributes,
	max_parallel_downloads: u32,
	finalized: NumberFor<B>,
	best_num: NumberFor<B>,
) -> Option<(Range<NumberFor<B>>, BlockRequest<B>)> {
	if best_num >= peer.best_number {
		// Will be downloaded as alternative fork instead.
		return None;
	}
	if peer.common_number < finalized {
		trace!(
			target: "sync",
			"Requesting pre-finalized chain from {:?}, common={}, finalized={}, peer best={}, our best={}",
			id, finalized, peer.common_number, peer.best_number, best_num,
		);
	}
	if let Some(range) = blocks.needed_blocks(
		id.clone(),
		MAX_BLOCKS_TO_REQUEST,
		peer.best_number,
		peer.common_number,
		max_parallel_downloads,
		MAX_DOWNLOAD_AHEAD,
	) {
		let request = message::generic::BlockRequest {
			id: 0,
			fields: attrs.clone(),
			from: message::FromBlock::Number(range.start),
			to: None,
			direction: message::Direction::Ascending,
			max: Some((range.end - range.start).saturated_into::<u32>())
		};
		Some((range, request))
	} else {
		None
	}
}

/// Get pending fork sync targets for a peer.
fn fork_sync_request<B: BlockT>(
	id: &PeerId,
	targets: &mut HashMap<B::Hash, ForkTarget<B>>,
	best_num: NumberFor<B>,
	finalized: NumberFor<B>,
	attributes: &message::BlockAttributes,
	check_block: impl Fn(&B::Hash) -> BlockStatus,
) -> Option<(B::Hash, BlockRequest<B>)>
{
	targets.retain(|hash, r| {
		if r.number <= finalized {
			trace!(target: "sync", "Removed expired fork sync request {:?} (#{})", hash, r.number);
			return false;
		}
		if check_block(hash) != BlockStatus::Unknown {
			trace!(target: "sync", "Removed obsolete fork sync request {:?} (#{})", hash, r.number);
			return false;
		}
		true
	});
	for (hash, r) in targets {
		if !r.peers.contains(id) {
			continue
		}
		if r.number <= best_num {
			let parent_status = r.parent_hash.as_ref().map_or(BlockStatus::Unknown, check_block);
			let mut count = (r.number - finalized).saturated_into::<u32>(); // up to the last finalized block
			if parent_status != BlockStatus::Unknown {
				// request only single block
				count = 1;
			}
			trace!(target: "sync", "Downloading requested fork {:?} from {}, {} blocks", hash, id, count);
			return Some((hash.clone(), message::generic::BlockRequest {
				id: 0,
				fields: attributes.clone(),
				from: message::FromBlock::Hash(hash.clone()),
				to: None,
				direction: message::Direction::Descending,
				max: Some(count),
			}))
		}
	}
	None
}

/// Returns `true` if the given `block` is a descendent of `base`.
fn is_descendent_of<Block, T>(client: &T, base: &Block::Hash, block: &Block::Hash) -> sp_blockchain::Result<bool>
	where
		Block: BlockT,
		T: HeaderMetadata<Block, Error = sp_blockchain::Error> + ?Sized,
{
	if base == block {
		return Ok(false);
	}

	let ancestor = sp_blockchain::lowest_common_ancestor(client, *block, *base)?;

	Ok(ancestor.hash == *base)
}

fn validate_blocks<Block: BlockT>(blocks: &Vec<message::BlockData<Block>>, who: &PeerId) -> Result<(), BadPeer> {
	for b in blocks {
		if let Some(header) = &b.header {
			let hash = header.hash();
			if hash != b.hash {
				debug!(
					target:"sync",
					"Bad header received from {}. Expected hash {:?}, got {:?}",
					who,
					b.hash,
					hash,
				);
				return Err(BadPeer(who.clone(), rep::BAD_BLOCK))
			}
		}
		if let (Some(header), Some(body)) = (&b.header, &b.body) {
			let expected = *header.extrinsics_root();
			let got = HashFor::<Block>::ordered_trie_root(body.iter().map(Encode::encode).collect());
			if expected != got {
				debug!(
					target:"sync",
					"Bad extrinsic root for a block {} received from {}. Expected {:?}, got {:?}",
					b.hash,
					who,
					expected,
					got,
				);
				return Err(BadPeer(who.clone(), rep::BAD_BLOCK))
			}
		}
	}
	Ok(())
}

#[cfg(test)]
mod test {
	use super::*;
	use super::message::FromBlock;
	use substrate_test_runtime_client::{
		runtime::Block,
		DefaultTestClientBuilderExt, TestClientBuilder, TestClientBuilderExt,
	};
	use sp_blockchain::HeaderBackend;
	use sc_block_builder::BlockBuilderProvider;
	use sp_consensus::block_validation::DefaultBlockAnnounceValidator;

	#[test]
	fn processes_empty_response_on_justification_request_for_unknown_block() {
		// if we ask for a justification for a given block to a peer that doesn't know that block
		// (different from not having a justification), the peer will reply with an empty response.
		// internally we should process the response as the justification not being available.

		let client = Arc::new(TestClientBuilder::new().build());
		let info = client.info();
		let block_announce_validator = Box::new(DefaultBlockAnnounceValidator::new(client.clone()));
		let peer_id = PeerId::random();

		let mut sync = ChainSync::new(
			Roles::AUTHORITY,
			client.clone(),
			&info,
			None,
			block_announce_validator,
			1,
		);

		let (a1_hash, a1_number) = {
			let a1 = client.new_block(Default::default()).unwrap().build().unwrap().block;
			(a1.hash(), *a1.header.number())
		};

		// add a new peer with the same best block
		sync.new_peer(peer_id.clone(), a1_hash, a1_number).unwrap();

		// and request a justification for the block
		sync.request_justification(&a1_hash, a1_number);

		// the justification request should be scheduled to that peer
		assert!(
			sync.justification_requests().any(|(who, request)| {
				who == peer_id && request.from == FromBlock::Hash(a1_hash)
			})
		);

		// there are no extra pending requests
		assert_eq!(
			sync.extra_justifications.pending_requests().count(),
			0,
		);

		// there's one in-flight extra request to the expected peer
		assert!(
			sync.extra_justifications.active_requests().any(|(who, (hash, number))| {
				*who == peer_id && *hash == a1_hash && *number == a1_number
			})
		);

		// if the peer replies with an empty response (i.e. it doesn't know the block),
		// the active request should be cleared.
		assert_eq!(
			sync.on_block_justification(
				peer_id.clone(),
				BlockResponse::<Block> {
					id: 0,
					blocks: vec![],
				}
			),
			Ok(OnBlockJustification::Nothing),
		);

		// there should be no in-flight requests
		assert_eq!(
			sync.extra_justifications.active_requests().count(),
			0,
		);

		// and the request should now be pending again, waiting for reschedule
		assert!(
			sync.extra_justifications.pending_requests().any(|(hash, number)| {
				*hash == a1_hash && *number == a1_number
			})
		);
	}
}
