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
use futures::executor::block_on;
use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
use sc_client_api::TransactionFor;
use sc_consensus::{BlockImport, BoxBlockImport, BoxJustificationImport};
use sc_keystore::LocalKeystore;
use sc_network_test::{Block as TestBlock, *};
use sp_application_crypto::key_types::SASSAFRAS;
use sp_consensus::{AlwaysCanAuthor, DisableProofRecording, NoNetwork as DummyOracle, Proposal};
use sp_consensus_sassafras::inherents::InherentDataProvider;
use sp_consensus_slots::SlotDuration;
use sp_runtime::{Digest, DigestItem};
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
		println!("IMPORT: {}", block.header.number);
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
		let slot_duration = config.slot_duration();

		let create_inherent_data_providers = Box::new(move |_, _| async move {
			let timestamp = TimestampInherentDataProvider::from_system_time();
			let slot =
				InherentDataProvider::from_timestamp_and_slot_duration(*timestamp, slot_duration);

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

struct DummyProposer {
	factory: DummyFactory,
	parent_hash: Hash,
	parent_number: u64,
	parent_slot: Slot,
}

impl Proposer<TestBlock> for DummyProposer {
	type Error = Error;
	type Transaction =
		sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>;
	type Proposal = future::Ready<Result<Proposal<TestBlock, Self::Transaction, ()>, Error>>;
	type ProofRecording = DisableProofRecording;
	type Proof = ();

	fn propose(
		self,
		_: InherentData,
		inherent_digests: Digest,
		_: Duration,
		_: Option<usize>,
	) -> Self::Proposal {
		let block_builder = self
			.factory
			.client
			.new_block_at(&BlockId::Hash(self.parent_hash), inherent_digests, false)
			.unwrap();

		let mut block = match block_builder.build().map_err(|e| e.into()) {
			Ok(b) => b.block,
			Err(e) => return future::ready(Err(e)),
		};

		println!("PROPOSING {}", block.header().number);

		let this_slot = crate::find_pre_digest::<TestBlock>(block.header())
			.expect("baked block has valid pre-digest")
			.slot;

		// figure out if we should add a consensus digest, since the test runtime doesn't.
		let epoch_changes = self.factory.epoch_changes.shared_data();
		let epoch = epoch_changes
			.epoch_data_for_child_of(
				descendent_query(&*self.factory.client),
				&self.parent_hash,
				self.parent_number,
				this_slot,
				|slot| Epoch::genesis(&self.factory.genesis_config, slot),
			)
			.expect("client has data to find epoch")
			.expect("can compute epoch for baked block");

		let first_in_epoch = self.parent_slot < epoch.start_slot;
		if first_in_epoch {
			// push a `Consensus` digest signalling next change.
			// we just reuse the same randomness and authorities as the prior
			// epoch. this will break when we add light client support, since
			// that will re-check the randomness logic off-chain.
			let digest_data = ConsensusLog::NextEpochData(NextEpochDescriptor {
				authorities: epoch.config.authorities.clone(),
				randomness: epoch.config.randomness,
				config: None,
			})
			.encode();
			let digest = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, digest_data);
			block.header.digest_mut().push(digest)
		}

		// mutate the block header according to the mutator.
		(self.factory.mutator)(&mut block.header, Stage::PreSeal);

		future::ready(Ok(Proposal { block, proof: (), storage_changes: Default::default() }))
	}
}

#[derive(Clone)]
struct DummyFactory {
	client: Arc<TestClient>,
	epoch_changes: SharedEpochChanges<TestBlock, Epoch>,
	genesis_config: SassafrasConfiguration,
	mutator: Mutator,
}

impl Environment<TestBlock> for DummyFactory {
	type CreateProposer = future::Ready<Result<DummyProposer, Error>>;
	type Proposer = DummyProposer;
	type Error = Error;

	fn init(&mut self, parent_header: &<TestBlock as BlockT>::Header) -> Self::CreateProposer {
		let parent_slot = crate::find_pre_digest::<TestBlock>(parent_header)
			.expect("parent header has a pre-digest")
			.slot;

		future::ready(Ok(DummyProposer {
			factory: self.clone(),
			parent_hash: parent_header.hash(),
			parent_number: *parent_header.number(),
			parent_slot,
		}))
	}
}

fn run_one_test(mutator: impl Fn(&mut TestHeader, Stage) + Send + Sync + 'static) {
	let mutator = Arc::new(mutator) as Mutator;

	MUTATOR.with(|m| *m.borrow_mut() = mutator.clone());
	let net = SassafrasTestNet::new(3);

	let peers = &[(0, "//Alice"), (1, "//Bob"), (2, "//Charlie")];

	let net = Arc::new(Mutex::new(net));
	let mut import_notifications = Vec::new();
	let mut sassafras_futures = Vec::new();
	let mut keystore_paths = Vec::new();

	for (peer_id, seed) in peers {
		let mut net = net.lock();
		let peer = net.peer(*peer_id);
		let client = peer.client().as_client();
		let select_chain = peer.select_chain().expect("Full client has select_chain");

		let keystore_path = tempfile::tempdir().expect("Creates keystore path");
		let keystore: SyncCryptoStorePtr =
			Arc::new(LocalKeystore::open(keystore_path.path(), None).expect("Creates keystore"));
		SyncCryptoStore::sr25519_generate_new(&*keystore, SASSAFRAS, Some(seed))
			.expect("Generates authority key");
		keystore_paths.push(keystore_path);

		let mut got_own = false;
		let mut got_other = false;

		let data = peer.data.as_ref().expect("babe link set up during initialization");

		let environ = DummyFactory {
			client: client.clone(),
			genesis_config: data.link.genesis_config.clone(),
			epoch_changes: data.link.epoch_changes.clone(),
			mutator: mutator.clone(),
		};

		import_notifications.push(
			// run each future until the imported block number is less than five and
			// we don't receive onw block produced by us and one produced by another peer.
			client
				.import_notification_stream()
				.take_while(move |n| {
					future::ready(
						n.header.number() < &5 || {
							if n.origin == BlockOrigin::Own {
								got_own = true;
							} else {
								got_other = true;
							}
							// continue until we have at least one block of our own
							// and one of another peer.
							!(got_own && got_other)
						},
					)
				})
				.for_each(|_| future::ready(())),
		);

		let sassafras_params = SassafrasParams {
			client: client.clone(),
			keystore,
			select_chain,
			env: environ,
			block_import: data.block_import.lock().take().expect("import set up during init"),
			sassafras_link: data.link.clone(),
			sync_oracle: DummyOracle,
			justification_sync_link: (),
			force_authoring: false,
			create_inherent_data_providers: move |_, _| async move {
				let timestamp = sp_timestamp::InherentDataProvider::from_system_time();

				let slot = InherentDataProvider::from_timestamp_and_slot_duration(
					*timestamp,
					SlotDuration::from_millis(6000),
				);
				Ok((timestamp, slot))
			},
			can_author_with: sp_consensus::AlwaysCanAuthor,
		};
		let sassafras_worker = start_sassafras(sassafras_params).unwrap();
		sassafras_futures.push(sassafras_worker);
	}

	block_on(future::select(
		futures::future::poll_fn(move |cx| {
			let mut net = net.lock();
			net.poll(cx);
			net.peers().iter().for_each(|peer| {
				peer.failed_verifications().iter().next().map(|(h, e)| {
					panic!("Verification failed for {:?}: {}", h, e);
				});
			});
			Poll::<()>::Pending
		}),
		future::select(future::join_all(import_notifications), future::join_all(sassafras_futures)),
	));
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

#[test]
fn authoring_blocks() {
	run_one_test(|_, _| ())
}
