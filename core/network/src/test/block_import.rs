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

//! Testing block import logic.

use consensus::import_queue::{
	import_single_block, IncomingBlock, BasicQueue, BlockImportError, BlockImportResult
};
use test_client::{self, prelude::*};
use test_client::runtime::{Block, Hash};
use runtime_primitives::generic::BlockId;
use super::*;

fn prepare_good_block() -> (TestClient, Hash, u64, PeerId, IncomingBlock<Block>) {
	let client = test_client::new();
	let block = client.new_block(Default::default()).unwrap().bake().unwrap();
	client.import(BlockOrigin::File, block).unwrap();

	let (hash, number) = (client.block_hash(1).unwrap().unwrap(), 1);
	let header = client.header(&BlockId::Number(1)).unwrap();
	let justification = client.justification(&BlockId::Number(1)).unwrap();
	let peer_id = PeerId::random();
	(client, hash, number, peer_id.clone(), IncomingBlock {
		hash,
		header,
		body: None,
		justification,
		origin: Some(peer_id.clone())
	})
}

#[test]
fn import_single_good_block_works() {
	let (_, _hash, number, peer_id, block) = prepare_good_block();
	match import_single_block(&mut test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))) {
		Ok(BlockImportResult::ImportedUnknown(ref num, ref aux, ref org))
			if *num == number && *aux == Default::default() && *org == Some(peer_id) => {}
		_ => panic!()
	}
}

#[test]
fn import_single_good_known_block_is_ignored() {
	let (mut client, _hash, number, _, block) = prepare_good_block();
	match import_single_block(&mut client, BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))) {
		Ok(BlockImportResult::ImportedKnown(ref n)) if *n == number => {}
		_ => panic!()
	}
}

#[test]
fn import_single_good_block_without_header_fails() {
	let (_, _, _, peer_id, mut block) = prepare_good_block();
	block.header = None;
	match import_single_block(&mut test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))) {
		Err(BlockImportError::IncompleteHeader(ref org)) if *org == Some(peer_id) => {}
		_ => panic!()
	}
}

#[test]
fn async_import_queue_drops() {
	// Perform this test multiple times since it exhibits non-deterministic behavior.
	for _ in 0..100 {
		let verifier = Arc::new(PassThroughVerifier(true));
		let queue = BasicQueue::new(verifier, Box::new(test_client::new()), None, None);
		drop(queue);
	}
}
