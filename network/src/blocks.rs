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
pub struct BlockData {
	pub block: message::BlockData,
	pub origin: PeerId,
}

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
		let count = count as BlockNumber;
		let (range, downloading) = {
			let mut downloading_iter = self.blocks.iter().peekable();
			loop {
				break match (downloading_iter.next(), downloading_iter.peek()) {
					(Some((start, &BlockRangeState::Downloading { ref len, downloading })), _) if downloading < MAX_PARALLEL_DOWNLOADS  =>
						(*start .. *start + *len, downloading),
					(Some((start, r)), Some(&(next_start, _))) if start + r.len() < *next_start =>
						(*start + r.len() .. cmp::min(*next_start, *start + count), 0), // gap
					(Some((start, r)), None) =>
						(start + r.len() .. start + r.len() + count, 0), // last range
					(None, _) =>
						(common .. common + count, 0), // empty
					_ => continue,
				}
			}
		};

		if range.start >= peer_best {
			return None;
		}

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
				assert!(from <= *start);
				match range_data {
					&mut BlockRangeState::Complete(ref mut blocks) if *start == prev => {
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
	use super::BlockCollection;
	use ethcore::client::{TestBlockChainClient, EachBlockWith, BlockId, BlockChainClient};
	use ethcore::views::HeaderView;
	use ethcore::header::BlockNumber;
	use rlp::*;

	fn is_empty(bc: &BlockCollection) -> bool {
		bc.heads.is_empty() &&
		bc.blocks.is_empty() &&
		bc.parents.is_empty() &&
		bc.header_ids.is_empty() &&
		bc.head.is_none() &&
		bc.downloading_headers.is_empty() &&
		bc.downloading_bodies.is_empty()
	}

	#[test]
	fn create_clear() {
		let mut bc = BlockCollection::new(false);
		assert!(is_empty(&bc));
		let client = TestBlockChainClient::new();
		client.add_blocks(100, EachBlockWith::Nothing);
		let hashes = (0 .. 100).map(|i| (&client as &BlockChainClient).block_hash(BlockId::Number(i)).unwrap()).collect();
		bc.reset_to(hashes);
		assert!(!is_empty(&bc));
		bc.clear();
		assert!(is_empty(&bc));
	}

	#[test]
	fn insert_headers() {
		let mut bc = BlockCollection::new(false);
		assert!(is_empty(&bc));
		let client = TestBlockChainClient::new();
		let nblocks = 200;
		client.add_blocks(nblocks, EachBlockWith::Nothing);
		let blocks: Vec<_> = (0..nblocks)
			.map(|i| (&client as &BlockChainClient).block(BlockId::Number(i as BlockNumber)).unwrap().into_inner())
			.collect();
		let headers: Vec<_> = blocks.iter().map(|b| Rlp::new(b).at(0).as_raw().to_vec()).collect();
		let hashes: Vec<_> = headers.iter().map(|h| HeaderView::new(h).hash()).collect();
		let heads: Vec<_> = hashes.iter().enumerate().filter_map(|(i, h)| if i % 20 == 0 { Some(h.clone()) } else { None }).collect();
		bc.reset_to(heads);
		assert!(!bc.is_empty());
		assert_eq!(hashes[0], bc.heads[0]);
		assert!(bc.needed_bodies(1, false).is_empty());
		assert!(!bc.contains(&hashes[0]));
		assert!(!bc.is_downloading(&hashes[0]));

		let (h, n) = bc.needed_headers(6, false).unwrap();
		assert!(bc.is_downloading(&hashes[0]));
		assert_eq!(hashes[0], h);
		assert_eq!(n, 6);
		assert_eq!(bc.downloading_headers.len(), 1);
		assert!(bc.drain().is_empty());

		bc.insert_headers(headers[0..6].to_vec());
		assert_eq!(hashes[5], bc.heads[0]);
		for h in &hashes[0..6] {
			bc.clear_header_download(h)
		}
		assert_eq!(bc.downloading_headers.len(), 0);
		assert!(!bc.is_downloading(&hashes[0]));
		assert!(bc.contains(&hashes[0]));

		assert_eq!(&bc.drain().into_iter().map(|b| b.block).collect::<Vec<_>>()[..], &blocks[0..6]);
		assert!(!bc.contains(&hashes[0]));
		assert_eq!(hashes[5], bc.head.unwrap());

		let (h, _) = bc.needed_headers(6, false).unwrap();
		assert_eq!(hashes[5], h);
		let (h, _) = bc.needed_headers(6, false).unwrap();
		assert_eq!(hashes[20], h);
		bc.insert_headers(headers[10..16].to_vec());
		assert!(bc.drain().is_empty());
		bc.insert_headers(headers[5..10].to_vec());
		assert_eq!(&bc.drain().into_iter().map(|b| b.block).collect::<Vec<_>>()[..], &blocks[6..16]);
		assert_eq!(hashes[15], bc.heads[0]);

		bc.insert_headers(headers[15..].to_vec());
		bc.drain();
		assert!(bc.is_empty());
	}

	#[test]
	fn insert_headers_with_gap() {
		let mut bc = BlockCollection::new(false);
		assert!(is_empty(&bc));
		let client = TestBlockChainClient::new();
		let nblocks = 200;
		client.add_blocks(nblocks, EachBlockWith::Nothing);
		let blocks: Vec<_> = (0..nblocks)
			.map(|i| (&client as &BlockChainClient).block(BlockId::Number(i as BlockNumber)).unwrap().into_inner())
			.collect();
		let headers: Vec<_> = blocks.iter().map(|b| Rlp::new(b).at(0).as_raw().to_vec()).collect();
		let hashes: Vec<_> = headers.iter().map(|h| HeaderView::new(h).hash()).collect();
		let heads: Vec<_> = hashes.iter().enumerate().filter_map(|(i, h)| if i % 20 == 0 { Some(h.clone()) } else { None }).collect();
		bc.reset_to(heads);

		bc.insert_headers(headers[2..22].to_vec());
		assert_eq!(hashes[0], bc.heads[0]);
		assert_eq!(hashes[21], bc.heads[1]);
		assert!(bc.head.is_none());
		bc.insert_headers(headers[0..2].to_vec());
		assert!(bc.head.is_some());
		assert_eq!(hashes[21], bc.heads[0]);
	}

	#[test]
	fn insert_headers_no_gap() {
		let mut bc = BlockCollection::new(false);
		assert!(is_empty(&bc));
		let client = TestBlockChainClient::new();
		let nblocks = 200;
		client.add_blocks(nblocks, EachBlockWith::Nothing);
		let blocks: Vec<_> = (0..nblocks)
			.map(|i| (&client as &BlockChainClient).block(BlockId::Number(i as BlockNumber)).unwrap().into_inner())
			.collect();
		let headers: Vec<_> = blocks.iter().map(|b| Rlp::new(b).at(0).as_raw().to_vec()).collect();
		let hashes: Vec<_> = headers.iter().map(|h| HeaderView::new(h).hash()).collect();
		let heads: Vec<_> = hashes.iter().enumerate().filter_map(|(i, h)| if i % 20 == 0 { Some(h.clone()) } else { None }).collect();
		bc.reset_to(heads);

		bc.insert_headers(headers[1..2].to_vec());
		assert!(bc.drain().is_empty());
		bc.insert_headers(headers[0..1].to_vec());
		assert_eq!(bc.drain().len(), 2);
	}
}

