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

use std::mem;
use std::cmp;
use std::ops::Range;
use std::collections::{HashMap, BTreeMap};
use std::collections::hash_map::Entry;
use network::PeerId;
use primitives::block::{Number as BlockNumber};
use message;

const MAX_PARALLEL_DOWNLOADS: u32 = 1;

/// Block data with origin.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BlockData {
	pub block: message::BlockData,
	pub origin: PeerId,
}

#[derive(Debug)]
enum BlockRangeState {
	Downloading {
		len: BlockNumber,
		downloading: u32,
	},
	Complete(Vec<BlockData>),
}

impl BlockRangeState {
	pub fn len(&self) -> BlockNumber {
		match *self {
			BlockRangeState::Downloading { len, .. } => len,
			BlockRangeState::Complete(ref blocks) => blocks.len() as BlockNumber,
		}
	}
}

/// A collection of blocks being downloaded.
#[derive(Default)]
pub struct BlockCollection {
	/// Downloaded blocks.
	blocks: BTreeMap<BlockNumber, BlockRangeState>,
	peer_requests: HashMap<PeerId, BlockNumber>,
}

impl BlockCollection {
	/// Create a new instance.
	pub fn new() -> BlockCollection {
		BlockCollection {
			blocks: BTreeMap::new(),
			peer_requests: HashMap::new(),
		}
	}

	/// Clear everything.
	pub fn clear(&mut self) {
		self.blocks.clear();
		self.peer_requests.clear();
	}

	/// Insert a set of blocks into collection.
	pub fn insert(&mut self, start: BlockNumber, blocks: Vec<message::BlockData>, peer_id: PeerId) {
		if blocks.is_empty() {
			return;
		}

		match self.blocks.get(&start) {
			Some(&BlockRangeState::Downloading { .. }) => {
				trace!(target: "sync", "Ignored block data still marked as being downloaded: {}", start);
				debug_assert!(false);
				return;
			},
			Some(&BlockRangeState::Complete(ref existing)) if existing.len() >= blocks.len() => {
				trace!(target: "sync", "Ignored block data already downloaded: {}", start);
				return;
			},
			_ => (),
		}

		self.blocks.insert(start, BlockRangeState::Complete(blocks.into_iter().map(|b| BlockData { origin: peer_id, block: b }).collect()));
	}

	/// Returns a set of block hashes that require a header download. The returned set is marked as being downloaded.
	pub fn needed_blocks(&mut self, peer_id: PeerId, count: usize, peer_best: BlockNumber, common: BlockNumber) -> Option<Range<BlockNumber>> {
		// First block number that we need to download
		let first_different = common + 1;
		let count = count as BlockNumber;
		let (mut range, downloading) = {
			let mut downloading_iter = self.blocks.iter().peekable();
			let mut prev: Option<(&BlockNumber, &BlockRangeState)> = None;
			loop {
				let next = downloading_iter.next();
				break match &(prev, next) {
					&(Some((start, &BlockRangeState::Downloading { ref len, downloading })), _) if downloading < MAX_PARALLEL_DOWNLOADS  =>
						(*start .. *start + *len, downloading),
					&(Some((start, r)), Some((next_start, _))) if start + r.len() < *next_start =>
						(*start + r.len() .. cmp::min(*next_start, *start + count), 0), // gap
					&(Some((start, r)), None) =>
						(start + r.len() .. start + r.len() + count, 0), // last range
					&(None, None) =>
						(first_different .. first_different + count, 0), // empty
					&(None, Some((start, _))) if *start > first_different =>
						(first_different .. cmp::min(first_different + count, *start), 0), // gap at the start
					_ => {
						prev = next;
						continue
					},
				}
			}
		};

		// crop to peers best
		if range.start >= peer_best {
			return None;
		}
		range.end = cmp::min(peer_best, range.end);

		self.peer_requests.insert(peer_id, range.start);
		self.blocks.insert(range.start, BlockRangeState::Downloading{ len: range.end - range.start, downloading: downloading + 1 });
		Some(range)
	}

	/// Get a valid chain of blocks ordered in descending order and ready for importing into blockchain.
	pub fn drain(&mut self, from: BlockNumber) -> Vec<BlockData> {
		let mut drained = Vec::new();
		let mut ranges = Vec::new();
		{
			let mut prev = from;
			for (start, range_data) in &mut self.blocks {
				match range_data {
					&mut BlockRangeState::Complete(ref mut blocks) if *start <= prev => {
							prev = *start + blocks.len() as BlockNumber;
							let mut blocks = mem::replace(blocks, Vec::new());
							drained.append(&mut blocks);
							ranges.push(*start);
					},
					_ => break,
				}
			}
		}
		for r in ranges {
			self.blocks.remove(&r);
		}
		trace!(target: "sync", "Drained {} blocks", drained.len());
		drained
	}

	pub fn clear_peer_download(&mut self, peer_id: PeerId) {
		match self.peer_requests.entry(peer_id) {
			Entry::Occupied(entry) => {
				let start = entry.remove();
				let remove = match self.blocks.get_mut(&start) {
					Some(&mut BlockRangeState::Downloading { ref mut downloading, .. }) if *downloading > 1 => {
						*downloading = *downloading - 1;
						false
					},
					Some(&mut BlockRangeState::Downloading { .. })  => {
						true
					},
					_ => {
						debug_assert!(false);
						false
					}
				};
				if remove {
					self.blocks.remove(&start);
				}
			},
			_ => (),
		}
	}
}

#[cfg(test)]
mod test {
	use super::{BlockCollection, BlockData};
	use message;
	use primitives::block::{HeaderHash};

	fn is_empty(bc: &BlockCollection) -> bool {
		bc.blocks.is_empty() &&
		bc.peer_requests.is_empty()
	}

	fn generate_blocks(n: usize) -> Vec<message::BlockData> {
		(0 .. n).map(|_| message::BlockData {
			hash: HeaderHash::random(),
			header: None,
			body: None,
			message_queue: None,
			receipt: None,
		}).collect()
	}

	#[test]
	fn create_clear() {
		let mut bc = BlockCollection::new();
		assert!(is_empty(&bc));
		bc.insert(1, generate_blocks(100),  0);
		assert!(!is_empty(&bc));
		bc.clear();
		assert!(is_empty(&bc));
	}

	#[test]
	fn insert_blocks() {
		let mut bc = BlockCollection::new();
		assert!(is_empty(&bc));
		let peer0 = 0;
		let peer1 = 1;
		let peer2 = 2;

		let blocks = generate_blocks(150);
		assert_eq!(bc.needed_blocks(peer0, 40, 150, 0), Some(1 .. 41));
		assert_eq!(bc.needed_blocks(peer1, 40, 150, 0), Some(41 .. 81));
		assert_eq!(bc.needed_blocks(peer2, 40, 150, 0), Some(81 .. 121));

		bc.clear_peer_download(peer1);
		bc.insert(41, blocks[41..81].to_vec(), peer1);
		assert_eq!(bc.drain(1), vec![]);
		assert_eq!(bc.needed_blocks(peer1, 40, 150, 0), Some(121 .. 150));
		bc.clear_peer_download(peer0);
		bc.insert(1, blocks[1..11].to_vec(), peer0);

		assert_eq!(bc.needed_blocks(peer0, 40, 150, 0), Some(11 .. 41));
		assert_eq!(bc.drain(1), blocks[1..11].iter().map(|b| BlockData { block: b.clone(), origin: 0 }).collect::<Vec<_>>());

		bc.clear_peer_download(peer0);
		bc.insert(11, blocks[11..41].to_vec(), peer0);

		let drained = bc.drain(12);
		assert_eq!(drained[..30], blocks[11..41].iter().map(|b| BlockData { block: b.clone(), origin: 0 }).collect::<Vec<_>>()[..]);
		assert_eq!(drained[30..], blocks[41..81].iter().map(|b| BlockData { block: b.clone(), origin: 1 }).collect::<Vec<_>>()[..]);

		bc.clear_peer_download(peer2);
		assert_eq!(bc.needed_blocks(peer2, 40, 150, 80), Some(81 .. 121));
		bc.clear_peer_download(peer2);
		bc.insert(81, blocks[81..121].to_vec(), peer2);
		bc.clear_peer_download(peer1);
		bc.insert(121, blocks[121..150].to_vec(), peer1);

		assert_eq!(bc.drain(80), vec![]);
		let drained = bc.drain(81);
		assert_eq!(drained[..40], blocks[81..121].iter().map(|b| BlockData { block: b.clone(), origin: 2 }).collect::<Vec<_>>()[..]);
		assert_eq!(drained[40..], blocks[121..150].iter().map(|b| BlockData { block: b.clone(), origin: 1 }).collect::<Vec<_>>()[..]);
	}
}

