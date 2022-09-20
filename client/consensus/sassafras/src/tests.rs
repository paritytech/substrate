// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Sassafras testsuite

#[allow(unused_imports)]
use super::*;
use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
use sc_client_api::TransactionFor;
use sc_consensus::{BlockImport, BoxBlockImport, BoxJustificationImport};
use sc_network_test::{Block as TestBlock, *};
use sp_consensus::AlwaysCanAuthor;
use sp_consensus_sassafras::inherents::InherentDataProvider;
use sp_consensus_slots::SlotDuration;
use std::{cell::RefCell, sync::Arc};

type TestHeader = <TestBlock as BlockT>::Header;

type Error = sp_blockchain::Error;

type TestClient = substrate_test_runtime_client::client::Client<
	substrate_test_runtime_client::Backend,
	substrate_test_runtime_client::ExecutorDispatch,
	TestBlock,
	substrate_test_runtime_client::runtime::RuntimeApi,
>;

type TestSelectChain =
	substrate_test_runtime_client::LongestChain<substrate_test_runtime_client::Backend, TestBlock>;

#[derive(Copy, Clone, PartialEq)]
enum Stage {
	PreSeal,
	PostSeal,
}

type Mutator = Arc<dyn Fn(&mut TestHeader, Stage) + Send + Sync>;

thread_local! {
	static MUTATOR: RefCell<Mutator> = RefCell::new(Arc::new(|_, _|()));
}

type SassafrasBlockImport = crate::SassafrasBlockImport<TestBlock, TestClient, Arc<TestClient>>;

#[derive(Clone)]
struct TestBlockImport {
	inner: SassafrasBlockImport,
}

#[async_trait::async_trait]
impl BlockImport<TestBlock> for TestBlockImport {
	type Error = <SassafrasBlockImport as BlockImport<TestBlock>>::Error;
	type Transaction = <SassafrasBlockImport as BlockImport<TestBlock>>::Transaction;

	async fn import_block(
		&mut self,
		block: BlockImportParams<TestBlock, Self::Transaction>,
		new_cache: HashMap<CacheKeyId, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		Ok(self.inner.import_block(block, new_cache).await.expect("importing block failed"))
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<TestBlock>,
	) -> Result<ImportResult, Self::Error> {
		Ok(self.inner.check_block(block).await.expect("checking block failed"))
	}
}

// TODO-SASS-P2: remove as soon as PR removing timestamp requirement is merged
use sp_timestamp::InherentDataProvider as TimestampInherentDataProvider;

type SassafrasVerifier = crate::SassafrasVerifier<
	TestBlock,
	PeersFullClient,
	TestSelectChain,
	AlwaysCanAuthor,
	Box<
		dyn CreateInherentDataProviders<
			TestBlock,
			(),
			InherentDataProviders = (TimestampInherentDataProvider, InherentDataProvider),
		>,
	>,
>;

pub struct TestVerifier {
	inner: SassafrasVerifier,
	mutator: Mutator,
}

#[async_trait::async_trait]
impl Verifier<TestBlock> for TestVerifier {
	/// Verify the given data and return the BlockImportParams and an optional
	/// new set of validators to import. If not, err with an Error-Message
	/// presented to the User in the logs.
	async fn verify(
		&mut self,
		mut block: BlockImportParams<TestBlock, ()>,
	) -> Result<(BlockImportParams<TestBlock, ()>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		// apply post-sealing mutations (i.e. stripping seal, if desired).
		(self.mutator)(&mut block.header, Stage::PostSeal);
		self.inner.verify(block).await
	}
}

struct PeerData {
	link: SassafrasLink<TestBlock>,
	block_import: Mutex<
		Option<
			BoxBlockImport<
				TestBlock,
				TransactionFor<substrate_test_runtime_client::Backend, TestBlock>,
			>,
		>,
	>,
}

type SassafrasPeer = Peer<Option<PeerData>, TestBlockImport>;

#[derive(Default)]
struct SassafrasTestNet {
	peers: Vec<SassafrasPeer>,
}

impl TestNetFactory for SassafrasTestNet {
	type BlockImport = TestBlockImport;
	type Verifier = TestVerifier;
	type PeerData = Option<PeerData>;

	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (
		BlockImportAdapter<Self::BlockImport>,
		Option<BoxJustificationImport<Block>>,
		Option<PeerData>,
	) {
		let client = client.as_client();

		let config = crate::configuration(&*client).expect("config available");
		let (inner, link) = crate::block_import(config, client.clone(), client.clone())
			.expect("can initialize block-import");

		let block_import = TestBlockImport { inner };

		let data_block_import =
			Mutex::new(Some(Box::new(block_import.clone()) as BoxBlockImport<_, _>));
		(
			BlockImportAdapter::new(block_import),
			None,
			Some(PeerData { link, block_import: data_block_import }),
		)
	}

	fn make_verifier(&self, client: PeersClient, maybe_link: &Option<PeerData>) -> Self::Verifier {
		use substrate_test_runtime_client::DefaultTestClientBuilderExt;

		let client = client.as_client();

		// ensure block import and verifier are linked correctly.
		let data = maybe_link
			.as_ref()
			.expect("babe link always provided to verifier instantiation");

		let (_, longest_chain) = TestClientBuilder::new().build_with_longest_chain();

		let config = crate::configuration(&*client).expect("config available");

		let create_inherent_data_providers = Box::new(|_, _| async {
			let timestamp = TimestampInherentDataProvider::from_system_time();
			let slot = InherentDataProvider::from_timestamp_and_slot_duration(
				*timestamp,
				SlotDuration::from_millis(6000),
			);

			Ok((timestamp, slot))
		});

		let inner = SassafrasVerifier::new(
			client.clone(),
			longest_chain,
			create_inherent_data_providers,
			data.link.epoch_changes.clone(),
			AlwaysCanAuthor,
			None,
			// TODO-SASS-P2: why babe doesn't have this???
			config,
		);

		TestVerifier { inner, mutator: MUTATOR.with(|m| m.borrow().clone()) }
	}

	fn peer(&mut self, i: usize) -> &mut SassafrasPeer {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<SassafrasPeer> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<SassafrasPeer>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}
}

#[test]
#[should_panic]
fn rejects_empty_block() {
	let mut net = SassafrasTestNet::new(3);
	let block_builder = |builder: BlockBuilder<_, _, _>| builder.build().unwrap().block;
	net.mut_peers(|peer| {
		peer[0].generate_blocks(1, BlockOrigin::NetworkInitialSync, block_builder);
	})
}
