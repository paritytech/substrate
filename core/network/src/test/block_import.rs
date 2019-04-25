// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Testing block import logic.

use consensus::import_queue::{import_single_block, BasicQueue, BlockImportError, BlockImportResult};
use test_client::{self, TestClient};
use test_client::runtime::{Block, Hash};
use runtime_primitives::generic::BlockId;
use super::*;

struct TestLink {}

impl Link<Block> for TestLink {}

fn prepare_good_block() -> (client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>, Hash, u64, PeerId, IncomingBlock<Block>) {
	let client = test_client::new();
	let block = client.new_block().unwrap().bake().unwrap();
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
	assert_eq!(
		import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Ok(BlockImportResult::ImportedUnknown(number, Default::default(), Some(peer_id)))
	);
}

#[test]
fn import_single_good_known_block_is_ignored() {
	let (client, _hash, number, _, block) = prepare_good_block();
	assert_eq!(
		import_single_block(&client, BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Ok(BlockImportResult::ImportedKnown(number))
	);
}

#[test]
fn import_single_good_block_without_header_fails() {
	let (_, _, _, peer_id, mut block) = prepare_good_block();
	block.header = None;
	assert_eq!(
		import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Err(BlockImportError::IncompleteHeader(Some(peer_id)))
	);
}

#[test]
fn async_import_queue_drops() {
	// Perform this test multiple times since it exhibits non-deterministic behavior.
	for _ in 0..100 {
		let verifier = Arc::new(PassThroughVerifier(true));
		let queue = BasicQueue::new(verifier, Arc::new(test_client::new()), None);
		queue.start(Box::new(TestLink{})).unwrap();
		drop(queue);
	}
}
