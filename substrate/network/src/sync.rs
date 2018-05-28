// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.?

use std::collections::HashMap;
use io::SyncIo;
use protocol::Protocol;
use network::PeerId;
use client::{ImportResult, BlockStatus, ClientInfo};
use primitives::block::{HeaderHash, Number as BlockNumber, Header, Id as BlockId};
use blocks::{self, BlockCollection};
use message::{self, Message};
use service::Role;
use super::header_hash;

// Maximum blocks to request in a single packet.
const MAX_BLOCKS_TO_REQUEST: usize = 128;

struct PeerSync {
	pub common_hash: HeaderHash,
	pub common_number: BlockNumber,
	pub best_hash: HeaderHash,
	pub best_number: BlockNumber,
	pub state: PeerSyncState,
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
enum PeerSyncState {
	AncestorSearch(BlockNumber),
	Available,
	DownloadingNew(BlockNumber),
	DownloadingStale(HeaderHash),
}

/// Relay chain sync strategy.
pub struct ChainSync {
	genesis_hash: HeaderHash,
	peers: HashMap<PeerId, PeerSync>,
	blocks: BlockCollection,
	best_queued_number: BlockNumber,
	best_queued_hash: HeaderHash,
	required_block_attributes: Vec<message::BlockAttribute>,
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
pub struct Status {
	/// Current global sync state.
	pub state: SyncState,
	/// Target sync block number.
	pub best_seen_block: Option<BlockNumber>,
}

impl ChainSync {
	/// Create a new instance.
	pub fn new(role: Role, info: &ClientInfo) -> ChainSync {
		let mut required_block_attributes = vec![
			message::BlockAttribute::Header,
			message::BlockAttribute::Justification
		];
		if role.intersects(Role::FULL | Role::VALIDATOR | Role::COLLATOR) {
			required_block_attributes.push(message::BlockAttribute::Body);
		}

		ChainSync {
			genesis_hash: info.chain.genesis_hash,
			peers: HashMap::new(),
			blocks: BlockCollection::new(),
			best_queued_hash: info.best_queued_hash.unwrap_or(info.chain.best_hash),
			best_queued_number: info.best_queued_number.unwrap_or(info.chain.best_number),
			required_block_attributes: required_block_attributes,
		}
	}

	fn best_seen_block(&self) -> Option<BlockNumber> {
		self.peers.values().max_by_key(|p| p.best_number).map(|p| p.best_number)
	}

	/// Returns sync status
	pub fn status(&self) -> Status {
		let best_seen = self.best_seen_block();
		let state = match &best_seen {
			&Some(n) if n > self.best_queued_number && n - self.best_queued_number > 5 => SyncState::Downloading,
			_ => SyncState::Idle,
		};
		Status {
			state: state,
			best_seen_block: best_seen,
		}
	}

	/// Handle new connected peer.
	pub fn new_peer(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId) {
		if let Some(info) = protocol.peer_info(peer_id) {
			match (protocol.chain().block_status(&BlockId::Hash(info.best_hash)), info.best_number) {
				(Err(e), _) => {
					debug!(target:"sync", "Error reading blockchain: {:?}", e);
					io.disconnect_peer(peer_id);
				},
				(Ok(BlockStatus::KnownBad), _) => {
					debug!(target:"sync", "New peer with known bad best block {} ({}).", info.best_hash, info.best_number);
					io.disable_peer(peer_id);
				},
				(Ok(BlockStatus::Unknown), 0) => {
					debug!(target:"sync", "New peer with unknown genesis hash {} ({}).", info.best_hash, info.best_number);
					io.disable_peer(peer_id);
				},
				(Ok(BlockStatus::Unknown), _) => {
					let our_best = self.best_queued_number;
					if our_best > 0 {
						debug!(target:"sync", "New peer with unknown best hash {} ({}), searching for common ancestor.", info.best_hash, info.best_number);
						self.peers.insert(peer_id, PeerSync {
							common_hash: self.genesis_hash,
							common_number: 0,
							best_hash: info.best_hash,
							best_number: info.best_number,
							state: PeerSyncState::AncestorSearch(our_best),
						});
						Self::request_ancestry(io, protocol, peer_id, our_best)
					} else {
						// We are at genesis, just start downloading
						debug!(target:"sync", "New peer with best hash {} ({}).", info.best_hash, info.best_number);
						self.peers.insert(peer_id, PeerSync {
							common_hash: self.genesis_hash,
							common_number: 0,
							best_hash: info.best_hash,
							best_number: info.best_number,
							state: PeerSyncState::Available,
						});
						self.download_new(io, protocol, peer_id)
					}
				},
				(Ok(BlockStatus::Queued), _) | (Ok(BlockStatus::InChain), _) => {
					debug!(target:"sync", "New peer with known best hash {} ({}).", info.best_hash, info.best_number);
					self.peers.insert(peer_id, PeerSync {
						common_hash: info.best_hash,
						common_number: info.best_number,
						best_hash: info.best_hash,
						best_number: info.best_number,
						state: PeerSyncState::Available,
					});
				}
			}
		}
	}

	pub fn on_block_data(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId, _request: message::BlockRequest, response: message::BlockResponse) {
		let count = response.blocks.len();
		let mut imported: usize = 0;
		let new_blocks = if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			match peer.state {
				PeerSyncState::DownloadingNew(start_block) => {
					self.blocks.clear_peer_download(peer_id);
					peer.state = PeerSyncState::Available;

					self.blocks.insert(start_block, response.blocks, peer_id);
					self.blocks.drain(self.best_queued_number + 1)
				},
				PeerSyncState::DownloadingStale(_) => {
					peer.state = PeerSyncState::Available;
					response.blocks.into_iter().map(|b| blocks::BlockData {
						origin: peer_id,
						block: b
					}).collect()
				},
				PeerSyncState::AncestorSearch(n) => {
					match response.blocks.get(0) {
						Some(ref block) => {
							trace!(target: "sync", "Got ancestry block #{} ({}) from peer {}", n, block.hash, peer_id);
							match protocol.chain().block_hash(n) {
								Ok(Some(block_hash)) if block_hash == block.hash => {
									peer.common_hash = block.hash;
									peer.common_number = n;
									peer.state = PeerSyncState::Available;
									trace!(target:"sync", "Found common ancestor for peer {}: {} ({})", peer_id, block.hash, n);
									vec![]
								},
								Ok(our_best) if n > 0 => {
									trace!(target:"sync", "Ancestry block mismatch for peer {}: theirs: {} ({}), ours: {:?}", peer_id, block.hash, n, our_best);
									let n = n - 1;
									peer.state = PeerSyncState::AncestorSearch(n);
									Self::request_ancestry(io, protocol, peer_id, n);
									return;
								},
								Ok(_) => { // genesis mismatch
									trace!(target:"sync", "Ancestry search: genesis mismatch for peer {}", peer_id);
									io.disable_peer(peer_id);
									return;
								},
								Err(e) => {
									debug!(target:"sync", "Error reading blockchain: {:?}", e);
									io.disconnect_peer(peer_id);
									return;
								}
							}
						},
						None => {
							trace!(target:"sync", "Invalid response when searching for ancestor from {}", peer_id);
							io.disconnect_peer(peer_id);
							return;
						}
					}
				},
				PeerSyncState::Available => Vec::new(),
			}
		} else {
			vec![]
		};

		let best_seen = self.best_seen_block();
		// Blocks in the response/drain should be in ascending order.
		for block in new_blocks {
			let origin = block.origin;
			let block = block.block;
			match (block.header, block.justification) {
				(Some(header), Some(justification)) => {
					let number = header.number;
					let hash = header_hash(&header);
					let parent = header.parent_hash;
					let is_best = best_seen.as_ref().map_or(false, |n| number >= *n);

					// check whether the block is known before importing.
					match protocol.chain().block_status(&BlockId::Hash(hash)) {
						Ok(BlockStatus::InChain) => continue,
						Ok(_) => {},
						Err(e) => {
							debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
							self.restart(io, protocol);
							return;
						}
					}

					let result = protocol.chain().import(
						is_best,
						header,
						justification,
						block.body
					);
					match result {
						Ok(ImportResult::AlreadyInChain) => {
							trace!(target: "sync", "Block already in chain {}: {:?}", number, hash);
							self.block_imported(&hash, number);
						},
						Ok(ImportResult::AlreadyQueued) => {
							trace!(target: "sync", "Block already queued {}: {:?}", number, hash);
							self.block_imported(&hash, number);
						},
						Ok(ImportResult::Queued) => {
							trace!(target: "sync", "Block queued {}: {:?}", number, hash);
							self.block_imported(&hash, number);
							imported = imported + 1;
						},
						Ok(ImportResult::UnknownParent) => {
							debug!(target: "sync", "Block with unknown parent {}: {:?}, parent: {:?}", number, hash, parent);
							self.restart(io, protocol);
							return;
						},
						Ok(ImportResult::KnownBad) => {
							debug!(target: "sync", "Bad block {}: {:?}", number, hash);
							io.disable_peer(origin); //TODO: use persistent ID
							self.restart(io, protocol);
							return;
						}
						Err(e) => {
							debug!(target: "sync", "Error importing block {}: {:?}: {:?}", number, hash, e);
							self.restart(io, protocol);
							return;
						}
					}
				},
				(None, _) => {
					debug!(target: "sync", "Header {} was not provided by {} ", block.hash, origin);
					io.disable_peer(origin); //TODO: use persistent ID
					return;
				},
				(_, None) => {
					debug!(target: "sync", "Justification set for block {} was not provided by {} ", block.hash, origin);
					io.disable_peer(origin); //TODO: use persistent ID
					return;
				}
			}
		}
		trace!(target: "sync", "Imported {} of {}", imported, count);
		self.maintain_sync(io, protocol);
	}

	fn maintain_sync(&mut self, io: &mut SyncIo, protocol: &Protocol) {
		let peers: Vec<PeerId> = self.peers.keys().map(|p| *p).collect();
		for peer in peers {
			self.download_new(io, protocol, peer);
		}
	}

	fn block_imported(&mut self, hash: &HeaderHash, number: BlockNumber) {
		if number > self.best_queued_number {
			self.best_queued_number = number;
			self.best_queued_hash = *hash;
		}
		// Update common blocks
		for (_, peer) in self.peers.iter_mut() {
			trace!("Updating peer info ours={}, theirs={}", number, peer.best_number);
			if peer.best_number >= number {
				peer.common_number = number;
				peer.common_hash = *hash;
			}
		}
	}

	pub fn update_chain_info(&mut self, best_header: &Header ) {
		let hash = header_hash(&best_header);
		self.block_imported(&hash, best_header.number)
	}

	pub fn on_block_announce(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId, hash: HeaderHash, header: &Header) {
		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			if header.number > peer.best_number {
				peer.best_number = header.number;
				peer.best_hash = hash;
			}
			if header.number <= self.best_queued_number && header.number > peer.common_number {
				peer.common_number = header.number;
			}
		} else {
			return;
		}

		if !self.is_known_or_already_downloading(protocol, &hash) {
			let stale = header.number <= self.best_queued_number;
			if stale {
				if !self.is_known_or_already_downloading(protocol, &header.parent_hash) {
					trace!(target: "sync", "Ignoring unknown stale block announce from {}: {} {:?}", peer_id, hash, header);
				} else {
					trace!(target: "sync", "Downloading new stale block announced from {}: {} {:?}", peer_id, hash, header);
					self.download_stale(io, protocol, peer_id, &hash);
				}
			} else {
				trace!(target: "sync", "Downloading new block announced from {}: {} {:?}", peer_id, hash, header);
				self.download_new(io, protocol, peer_id);
			}
		} else {
			trace!(target: "sync", "Known block announce from {}: {}", peer_id, hash);
		}
	}

	fn is_known_or_already_downloading(&self, protocol: &Protocol, hash: &HeaderHash) -> bool {
		self.peers.iter().any(|(_, p)| p.state == PeerSyncState::DownloadingStale(*hash))
			|| protocol.chain().block_status(&BlockId::Hash(*hash)).ok().map_or(false, |s| s != BlockStatus::Unknown)
	}

	pub fn peer_disconnected(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId) {
		self.blocks.clear_peer_download(peer_id);
		self.peers.remove(&peer_id);
		self.maintain_sync(io, protocol);
	}

	pub fn restart(&mut self, io: &mut SyncIo, protocol: &Protocol) {
		self.blocks.clear();
		let ids: Vec<PeerId> = self.peers.keys().map(|p| *p).collect();
		for id in ids {
			self.new_peer(io, protocol, id);
		}
		match protocol.chain().info() {
			Ok(info) => {
				self.best_queued_hash = info.best_queued_hash.unwrap_or(info.chain.best_hash);
				self.best_queued_number = info.best_queued_number.unwrap_or(info.chain.best_number);
			},
			Err(e) => {
				debug!(target:"sync", "Error reading blockchain: {:?}", e);
				self.best_queued_hash = self.genesis_hash;
				self.best_queued_number = 0;
			}
		}
	}

	pub fn clear(&mut self) {
		self.blocks.clear();
		self.peers.clear();
	}

	// Download old block.
	fn download_stale(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId, hash: &HeaderHash) {
		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			match peer.state {
				PeerSyncState::Available => {
					let request = message::BlockRequest {
						id: 0,
						fields: self.required_block_attributes.clone(),
						from: message::FromBlock::Hash(*hash),
						to: None,
						direction: message::Direction::Ascending,
						max: Some(1),
					};
					peer.state = PeerSyncState::DownloadingStale(*hash);
					protocol.send_message(io, peer_id, Message::BlockRequest(request));
				},
				_ => (),
			}
		}
	}

	// Issue a request for a peer to download new blocks, if any are available
	fn download_new(&mut self, io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId) {
		if let Some(ref mut peer) = self.peers.get_mut(&peer_id) {
			trace!(target: "sync", "Considering new block download from {}, common block is {}, best is {:?}", peer_id, peer.common_number, peer.best_number);
			match peer.state {
				PeerSyncState::Available => {
					if let Some(range) = self.blocks.needed_blocks(peer_id, MAX_BLOCKS_TO_REQUEST, peer.best_number, peer.common_number) {
						trace!(target: "sync", "Requesting blocks from {}, ({} to {})", peer_id, range.start, range.end);
						let request = message::BlockRequest {
							id: 0,
							fields: self.required_block_attributes.clone(),
							from: message::FromBlock::Number(range.start),
							to: None,
							direction: message::Direction::Ascending,
							max: Some((range.end - range.start) as u32),
						};
						peer.state = PeerSyncState::DownloadingNew(range.start);
						protocol.send_message(io, peer_id, Message::BlockRequest(request));
					} else {
						trace!(target: "sync", "Nothing to request");
					}
				},
				_ => (),
			}
		}
	}

	fn request_ancestry(io: &mut SyncIo, protocol: &Protocol, peer_id: PeerId, block: BlockNumber) {
		trace!(target: "sync", "Requesting ancestry block #{} from {}", block, peer_id);
		let request = message::BlockRequest {
			id: 0,
			fields: vec![message::BlockAttribute::Header, message::BlockAttribute::Justification],
			from: message::FromBlock::Number(block),
			to: None,
			direction: message::Direction::Ascending,
			max: Some(1),
		};
		protocol.send_message(io, peer_id, Message::BlockRequest(request));
	}
}
