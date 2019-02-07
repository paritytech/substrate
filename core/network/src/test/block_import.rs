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

//! Testing block import logic.

use consensus::import_queue::{import_single_block, process_import_result};
use consensus::import_queue::{AsyncImportQueueData, BasicQueue, BlockImportError, BlockImportResult};
use test_client::{self, TestClient};
use test_client::runtime::{Block, Hash};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::NumberFor;
use std::cell::Cell;
use super::*;

struct TestLink {
	imported: Cell<usize>,
	maintains: Cell<usize>,
	disconnects: Cell<usize>,
	restarts: Cell<usize>,
}

impl TestLink {
	fn new() -> TestLink {
		TestLink {
			imported: Cell::new(0),
			maintains: Cell::new(0),
			disconnects: Cell::new(0),
			restarts: Cell::new(0),
		}
	}

	fn total(&self) -> usize {
		self.imported.get() + self.maintains.get() + self.disconnects.get() + self.restarts.get()
	}
}

impl Link<Block> for TestLink {
	fn block_imported(&self, _hash: &Hash, _number: NumberFor<Block>) {
		self.imported.set(self.imported.get() + 1);
	}
	fn maintain_sync(&self) {
		self.maintains.set(self.maintains.get() + 1);
	}
	fn useless_peer(&self, _: NodeIndex, _: &str) {
		self.disconnects.set(self.disconnects.get() + 1);
	}
	fn note_useless_and_restart_sync(&self, id: NodeIndex, r: &str) {
		self.useless_peer(id, r);
		self.restart();
	}
	fn restart(&self) {
		self.restarts.set(self.restarts.get() + 1);
	}
}

fn prepare_good_block() -> (client::Client<test_client::Backend, test_client::Executor, Block, test_client::runtime::RuntimeApi>, Hash, u64, IncomingBlock<Block>) {
	let client = test_client::new();
	let block = client.new_block().unwrap().bake().unwrap();
	client.import(BlockOrigin::File, block).unwrap();

	let (hash, number) = (client.block_hash(1).unwrap().unwrap(), 1);
	let header = client.header(&BlockId::Number(1)).unwrap();
	let justification = client.justification(&BlockId::Number(1)).unwrap();
	(client, hash, number, IncomingBlock {
		hash,
		header,
		body: None,
		justification,
		origin: Some(0)
	})
}

#[test]
fn import_single_good_block_works() {
	let (_, hash, number, block) = prepare_good_block();
	assert_eq!(
		import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Ok(BlockImportResult::ImportedUnknown(hash, number))
	);
}

#[test]
fn import_single_good_known_block_is_ignored() {
	let (client, hash, number, block) = prepare_good_block();
	assert_eq!(
		import_single_block(&client, BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Ok(BlockImportResult::ImportedKnown(hash, number))
	);
}

#[test]
fn import_single_good_block_without_header_fails() {
	let (_, _, _, mut block) = prepare_good_block();
	block.header = None;
	assert_eq!(
		import_single_block(&test_client::new(), BlockOrigin::File, block, Arc::new(PassThroughVerifier(true))),
		Err(BlockImportError::IncompleteHeader(Some(0)))
	);
}

#[test]
fn process_import_result_works() {
	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedKnown(Default::default(), 0))), 1);
	assert_eq!(link.total(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedKnown(Default::default(), 0))), 1);
	assert_eq!(link.total(), 1);
	assert_eq!(link.imported.get(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Ok(BlockImportResult::ImportedUnknown(Default::default(), 0))), 1);
	assert_eq!(link.total(), 1);
	assert_eq!(link.imported.get(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::IncompleteHeader(Some(0)))), 0);
	assert_eq!(link.total(), 2);
	assert_eq!(link.disconnects.get(), 1);
	assert_eq!(link.restarts.get(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::UnknownParent)), 0);
	assert_eq!(link.total(), 1);
	assert_eq!(link.restarts.get(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::Error)), 0);
	assert_eq!(link.total(), 1);
	assert_eq!(link.restarts.get(), 1);

	let link = TestLink::new();
	assert_eq!(process_import_result::<Block>(&link, Err(BlockImportError::VerificationFailed(Some(0), String::new()))), 0);
	assert_eq!(link.total(), 2);
	assert_eq!(link.restarts.get(), 1);
	assert_eq!(link.disconnects.get(), 1);
}

#[test]
fn import_many_blocks_stops_when_stopping() {
	let (_, _, _, block) = prepare_good_block();
	let qdata = AsyncImportQueueData::new();
	let verifier = Arc::new(PassThroughVerifier(true));
	qdata.stop();
	let client = test_client::new();
	assert!(!import_many_blocks(
		&client,
		&mut TestLink::new(),
		Some(&qdata),
		(BlockOrigin::File, vec![block.clone(), block]),
		verifier
	));
}

#[test]
fn async_import_queue_drops() {
	// Perform this test multiple times since it exhibits non-deterministic behavior.
	for _ in 0..100 {
		let verifier = Arc::new(PassThroughVerifier(true));
		let queue = BasicQueue::new(verifier, Arc::new(test_client::new()), None);
		queue.start(TestLink::new()).unwrap();
		drop(queue);
	}
}
