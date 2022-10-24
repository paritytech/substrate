// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Sassafras client tests

#[allow(unused_imports)]
use super::*;

use futures::executor::block_on;
use std::sync::Arc;

use sc_block_builder::BlockBuilderProvider;
use sc_client_api::Finalizer;
use sc_consensus::{BlockImport, BoxJustificationImport};
use sc_network_test::*;
use sp_application_crypto::key_types::SASSAFRAS;
use sp_blockchain::Error as TestError;
use sp_consensus::{DisableProofRecording, NoNetwork as DummyOracle, Proposal};
use sp_consensus_sassafras::inherents::InherentDataProvider;
use sp_keyring::Sr25519Keyring;
use sp_keystore::testing::KeyStore as TestKeyStore;
use sp_runtime::{Digest, DigestItem};
use sp_timestamp::Timestamp;

use substrate_test_runtime_client::{runtime::Block as TestBlock, Backend as TestBackend};

type TestHeader = <TestBlock as BlockT>::Header;

type TestClient = substrate_test_runtime_client::client::Client<
	TestBackend,
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

type SassafrasIntermediate = crate::SassafrasIntermediate<TestBlock>;

type SassafrasBlockImport = crate::SassafrasBlockImport<TestBlock, TestClient, Arc<TestClient>>;

type SassafrasVerifier = crate::SassafrasVerifier<
	TestBlock,
	PeersFullClient,
	TestSelectChain,
	Box<
		dyn CreateInherentDataProviders<
			TestBlock,
			(),
			InherentDataProviders = (InherentDataProvider,),
		>,
	>,
>;

type SassafrasLink = crate::SassafrasLink<TestBlock>;

type BlockId = crate::BlockId<TestBlock>;

struct DummyProposer {
	factory: TestEnvironment,
	parent_hash: Hash,
	parent_number: u64,
	parent_slot: Slot,
}

impl DummyProposer {
	fn propose_block(self, digest: Digest) -> TestBlock {
		block_on(self.propose(InherentData::default(), digest, Duration::default(), None))
			.expect("Proposing block")
			.block
	}
}

impl Proposer<TestBlock> for DummyProposer {
	type Error = TestError;
	type Transaction =
		sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>;
	type Proposal = future::Ready<Result<Proposal<TestBlock, Self::Transaction, ()>, Self::Error>>;
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

		// Currently the test runtime doesn't invoke each pallet Hooks such as `on_initialize` and
		// `on_finalize`. Thus we have to manually figure out if we should add a consensus digest.

		let this_slot = crate::find_pre_digest::<TestBlock>(block.header())
			.expect("baked block has valid pre-digest")
			.slot;

		let epoch_changes = self.factory.link.epoch_changes.shared_data();
		let epoch = epoch_changes
			.epoch_data_for_child_of(
				descendent_query(&*self.factory.client),
				&self.parent_hash,
				self.parent_number,
				this_slot,
				|slot| Epoch::genesis(&self.factory.link.genesis_config, slot),
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

		future::ready(Ok(Proposal { block, proof: (), storage_changes: Default::default() }))
	}
}

type Mutator = Arc<dyn Fn(&mut TestHeader, Stage) + Send + Sync>;

#[derive(Clone)]
struct TestEnvironment {
	client: Arc<TestClient>,
	backend: Arc<TestBackend>,
	block_import: SassafrasBlockImport,
	link: SassafrasLink,
	mutator: Option<Mutator>,
}

impl TestEnvironment {
	fn new(mutator: Option<Mutator>) -> Self {
		let (client, backend) = TestClientBuilder::with_default_backend().build_with_backend();
		let client = Arc::new(client);

		// Note: configuration is loaded using the `TestClient` instance as the runtime-api
		// provider. In practice this will use the values defined within the test runtime
		// defined in the `substrate_test_runtime` crate.
		let config = crate::configuration(&*client).expect("config available");
		let (block_import, link) = crate::block_import(config, client.clone(), client.clone())
			.expect("can initialize block-import");

		Self { client, backend, block_import, link, mutator }
	}

	fn new_with_pre_built_data(
		client: Arc<TestClient>,
		backend: Arc<TestBackend>,
		block_import: SassafrasBlockImport,
		link: SassafrasLink,
		mutator: Option<Mutator>,
	) -> Self {
		Self { client, backend, block_import, link, mutator }
	}

	// Propose and import a new Sassafras block on top of the given parent.
	// This skips verification.
	fn propose_and_import_block(&mut self, parent_id: BlockId, slot: Option<Slot>) -> Hash {
		let parent = self.client.header(&parent_id).unwrap().unwrap();

		let proposer = block_on(self.init(&parent)).unwrap();

		let slot = slot.unwrap_or_else(|| {
			let parent_pre_digest = find_pre_digest::<TestBlock>(&parent).unwrap();
			parent_pre_digest.slot + 1
		});

		let pre_digest = PreDigest {
			slot,
			authority_idx: 0,
			vrf_output: VRFOutput::try_from([0; 32]).unwrap(),
			vrf_proof: VRFProof::try_from([0; 64]).unwrap(),
			ticket_aux: None,
		};
		let digest = sp_runtime::generic::Digest {
			logs: vec![DigestItem::sassafras_pre_digest(pre_digest)],
		};

		let mut block = proposer.propose_block(digest);

		let epoch_descriptor = self
			.link
			.epoch_changes
			.shared_data()
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent.hash(),
				*parent.number(),
				slot,
			)
			.unwrap()
			.unwrap();

		if let Some(ref mutator) = self.mutator {
			(mutator)(&mut block.header, Stage::PreSeal);
		}

		let seal = {
			// Sign the pre-sealed hash of the block and then add it to a digest item.
			let pair = AuthorityPair::from_seed(&[1; 32]);
			let pre_hash = block.header.hash();
			let signature = pair.sign(pre_hash.as_ref());
			DigestItem::sassafras_seal(signature)
		};

		let post_hash = {
			block.header.digest_mut().push(seal.clone());
			let h = block.header.hash();
			block.header.digest_mut().pop();
			h
		};

		if let Some(ref mutator) = self.mutator {
			(mutator)(&mut block.header, Stage::PostSeal);
		}

		let mut import = BlockImportParams::new(BlockOrigin::Own, block.header);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		import.body = Some(block.extrinsics);
		import.post_digests.push(seal);
		import.insert_intermediate(INTERMEDIATE_KEY, SassafrasIntermediate { epoch_descriptor });

		match block_on(self.block_import.import_block(import, Default::default())).unwrap() {
			ImportResult::Imported(_) => (),
			_ => panic!("expected block to be imported"),
		}

		post_hash
	}

	// Propose and import n valid Sassafras blocks that are built on top of the given parent.
	// The proposer takes care of producing epoch change digests according to the epoch
	// duration (which is set to 6 slots in the test runtime).
	fn propose_and_import_blocks(&mut self, mut parent_id: BlockId, n: usize) -> Vec<Hash> {
		let mut hashes = Vec::with_capacity(n);

		for _ in 0..n {
			let hash = self.propose_and_import_block(parent_id, None);
			hashes.push(hash);
			parent_id = BlockId::Hash(hash);
		}

		hashes
	}
}

impl Environment<TestBlock> for TestEnvironment {
	type CreateProposer = future::Ready<Result<DummyProposer, TestError>>;
	type Proposer = DummyProposer;
	type Error = TestError;

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

fn create_keystore(authority: Sr25519Keyring) -> SyncCryptoStorePtr {
	let keystore = Arc::new(TestKeystore::new());
	SyncCryptoStore::sr25519_generate_new(&*keystore, SASSAFRAS, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore
}

#[test]
#[should_panic(expected = "valid sassafras headers must contain a predigest")]
fn rejects_block_without_pre_digest() {
	let mutator = Arc::new(|header: &mut TestHeader, stage| {
		if stage == Stage::PreSeal {
			header.digest.logs.clear()
		}
	});

	let mut env = TestEnvironment::new(Some(mutator));

	env.propose_and_import_block(BlockId::Number(0), Some(999.into()));
}

#[test]
fn importing_block_one_sets_genesis_epoch() {
	let mut env = TestEnvironment::new(None);

	let block_hash = env.propose_and_import_block(BlockId::Number(0), Some(999.into()));

	let genesis_epoch = Epoch::genesis(&env.link.genesis_config, 999.into());

	let epoch_changes = env.link.epoch_changes.shared_data();

	let epoch_for_second_block = epoch_changes
		.epoch_data_for_child_of(
			descendent_query(&*env.client),
			&block_hash,
			1,
			1000.into(),
			|slot| Epoch::genesis(&env.link.genesis_config, slot),
		)
		.unwrap()
		.unwrap();

	assert_eq!(epoch_for_second_block, genesis_epoch);
}

// TODO-SASS-P2: test import blocks with tickets aux data
// TODO-SASS-P2: test finalization prunes tree

#[test]
fn import_block_with_ticket_proof() {
	let mut env = TestEnvironment::new(None);

	let blocks = env.propose_and_import_blocks(BlockId::Number(0), 7);
}

#[test]
fn finalization_prunes_epoch_changes_tree() {}

#[test]
fn allows_to_skip_epochs() {
	// Test scenario.
	// Epoch lenght: 6 slots
	//
	// Block# :  [ 1 2 3 4 5 6 ][ 7 - -  -  -  - ][  -  -  -  -  -  - ][  8  ... ]
	// Slot#  :  [ 1 2 3 4 5 6 ][ 7 8 9 10 11 12 ][ 13 14 15 16 17 18 ][ 19  ... ]
	// Epoch# :  [      0      ][       1        ][      skipped      ][    3    ]
	//
	// As a recovery strategy, a fallback epoch 3 is created by reusing part of the
	// configuration created for epoch 2.
	let mut env = TestEnvironment::new(None);

	let blocks = env.propose_and_import_blocks(BlockId::Number(0), 7);

	// First block after the a skipped epoch (block #8 @ slot #19)
	let block =
		env.propose_and_import_block(BlockId::Hash(*blocks.last().unwrap()), Some(19.into()));

	let epoch_changes = env.link.epoch_changes.shared_data();
	let epochs: Vec<_> = epoch_changes.tree().iter().collect();
	assert_eq!(epochs.len(), 3);
	assert_eq!(*epochs[0].0, blocks[0]);
	assert_eq!(*epochs[0].1, 1);
	assert_eq!(*epochs[1].0, blocks[6]);
	assert_eq!(*epochs[1].1, 7);
	assert_eq!(*epochs[2].0, block);
	assert_eq!(*epochs[2].1, 8);

	// Fist block in E0 (B1)) announces E0 (this is special)
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Genesis0,
			hash: blocks[0],
			number: 1,
		})
		.unwrap();
	assert_eq!(data.epoch_index, 0);
	assert_eq!(data.start_slot, Slot::from(1));

	// First block in E0 (B1) also announces E1
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Genesis1,
			hash: blocks[0],
			number: 1,
		})
		.unwrap();
	assert_eq!(data.epoch_index, 1);
	assert_eq!(data.start_slot, Slot::from(7));

	// First block in E1 (B7) announces E2
	// NOTE: config has been "magically" used by E3 without altering epoch node values.
	// This will break as soon as our assumptions about how fork-tree works are not met anymore
	// (and this is a good thing)
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: blocks[6],
			number: 7,
		})
		.unwrap();
	assert_eq!(data.epoch_index, 2);
	assert_eq!(data.start_slot, Slot::from(13));

	// First block in E3 (B8) announced E4.
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: block,
			number: 8,
		})
		.unwrap();
	assert_eq!(data.epoch_index, 4);
	assert_eq!(data.start_slot, Slot::from(25));
}

#[test]
fn revert_prunes_epoch_changes_and_removes_weights() {
	let mut env = TestEnvironment::new(None);

	// Test scenario.
	// X(#y): a block (number y) announcing the next epoch data.
	// Information for epoch starting at block #19 is produced on three different forks
	// at block #13.
	// One branch starts before the revert point (epoch data should be maintained).
	// One branch starts after the revert point (epoch data should be removed).
	//
	//                        *----------------- F(#13) --#18                  < fork #2
	//                       /
	// A(#1) ---- B(#7) ----#8----+-----#12----- C(#13) ---- D(#19) ------#21  < canon
	//   \                        ^       \
	//    \                    revert      *---- G(#13) ---- H(#19) ---#20     < fork #3
	//     \                   to #10
	//      *-----E(#7)---#11                                          < fork #1

	let canon = env.propose_and_import_blocks(BlockId::Number(0), 21);
	let fork1 = env.propose_and_import_blocks(BlockId::Hash(canon[0]), 10);
	let fork2 = env.propose_and_import_blocks(BlockId::Hash(canon[7]), 10);
	let fork3 = env.propose_and_import_blocks(BlockId::Hash(canon[11]), 8);

	let epoch_changes = env.link.epoch_changes.clone();

	// We should be tracking a total of 9 epochs in the fork tree
	assert_eq!(epoch_changes.shared_data().tree().iter().count(), 8);
	// And only one root
	assert_eq!(epoch_changes.shared_data().tree().roots().count(), 1);

	// Revert canon chain to block #10 (best(21) - 11)
	crate::revert(env.backend.clone(), 11).unwrap();

	// Load and check epoch changes.

	let actual_nodes = aux_schema::load_epoch_changes::<TestBlock, TestClient>(&*env.client)
		.unwrap()
		.shared_data()
		.tree()
		.iter()
		.map(|(h, _, _)| *h)
		.collect::<Vec<_>>();

	let expected_nodes = vec![
		canon[0], // A
		canon[6], // B
		fork2[4], // F
		fork1[5], // E
	];

	assert_eq!(actual_nodes, expected_nodes);

	let weight_data_check = |hashes: &[Hash], expected: bool| {
		hashes.iter().all(|hash| {
			aux_schema::load_block_weight(&*env.client, hash).unwrap().is_some() == expected
		})
	};
	assert!(weight_data_check(&canon[..10], true));
	assert!(weight_data_check(&canon[10..], false));
	assert!(weight_data_check(&fork1, true));
	assert!(weight_data_check(&fork2, true));
	assert!(weight_data_check(&fork3, false));
}

#[test]
fn revert_not_allowed_for_finalized() {
	let mut env = TestEnvironment::new(None);

	let canon = env.propose_and_import_blocks(BlockId::Number(0), 3);

	// Finalize best block
	env.client.finalize_block(BlockId::Hash(canon[2]), None, false).unwrap();

	// Revert canon chain to last finalized block
	crate::revert(env.backend.clone(), 100).expect("revert should work for baked test scenario");

	let weight_data_check = |hashes: &[Hash], expected: bool| {
		hashes.iter().all(|hash| {
			aux_schema::load_block_weight(&*env.client, hash).unwrap().is_some() == expected
		})
	};
	assert!(weight_data_check(&canon, true));
}

////=================================================================================================
//// More complex tests involving communication between multiple nodes.
////
//// These tests are performed via a specially crafted test network.
////=================================================================================================

struct PeerData {
	link: SassafrasLink,
	block_import: SassafrasBlockImport,
}

type SassafrasPeer = Peer<Option<PeerData>, SassafrasBlockImport>;

#[derive(Default)]
struct SassafrasTestNet {
	peers: Vec<SassafrasPeer>,
}

impl TestNetFactory for SassafrasTestNet {
	type BlockImport = SassafrasBlockImport;
	type Verifier = SassafrasVerifier;
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
		let (block_import, link) = crate::block_import(config, client.clone(), client.clone())
			.expect("can initialize block-import");

		(BlockImportAdapter::new(block_import.clone()), None, Some(PeerData { link, block_import }))
	}

	fn make_verifier(&self, client: PeersClient, maybe_link: &Option<PeerData>) -> Self::Verifier {
		use substrate_test_runtime_client::DefaultTestClientBuilderExt;

		let client = client.as_client();

		let data = maybe_link.as_ref().expect("data provided to verifier instantiation");

		let config = crate::configuration(&*client).expect("config available");
		let slot_duration = config.slot_duration();

		let create_inherent_data_providers = Box::new(move |_, _| async move {
			let slot = InherentDataProvider::from_timestamp_and_slot_duration(
				Timestamp::current(),
				slot_duration,
			);
			Ok((slot,))
		});

		let (_, longest_chain) = TestClientBuilder::new().build_with_longest_chain();

		SassafrasVerifier::new(
			client.clone(),
			longest_chain,
			create_inherent_data_providers,
			data.link.epoch_changes.clone(),
			None,
			// TODO-SASS-P2: why babe doesn't have this config???
			config,
		)
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

// Multiple nodes authoring and validating blocks
#[test]
fn sassafras_network_progress() {
	let net = SassafrasTestNet::new(3);
	let net = Arc::new(Mutex::new(net));

	let peers =
		&[(0, Sr25519Keyring2::Alice), (1, Sr25519Keyring::Bob), (2, Sr25519Keyring::Charlie)];

	let mut import_notifications = Vec::new();
	let mut sassafras_workers = Vec::new();

	for (peer_id, auth_id) in peers {
		let mut net = net.lock();
		let peer = net.peer(*peer_id);
		let client = peer.client().as_client();
		let backend = peer.client().as_backend();
		let select_chain = peer.select_chain().expect("Full client has select_chain");

		let keystore = create_keystore(auth_id);

		let data = peer.data.as_ref().expect("sassafras link set up during initialization");

		let env = TestEnvironment::new_with_pre_built_data(
			client.clone(),
			backend.clone(),
			data.block_import.clone(),
			data.link.clone(),
			None,
		);

		// Run the imported block number is less than five and we don't receive a block produced
		// by us and one produced by another peer.
		let mut got_own = false;
		let mut got_other = false;
		let import_futures = client
			.import_notification_stream()
			.take_while(move |n| {
				future::ready(
					n.header.number() < &5 || {
						if n.origin == BlockOrigin::Own {
							got_own = true;
						} else {
							got_other = true;
						}
						!(got_own && got_other)
					},
				)
			})
			.for_each(|_| future::ready(()));
		import_notifications.push(import_futures);

		let slot_duration = data.link.genesis_config.slot_duration();
		let create_inherent_data_providers = Box::new(move |_, _| async move {
			let slot = InherentDataProvider::from_timestamp_and_slot_duration(
				Timestamp::current(),
				slot_duration,
			);
			Ok((slot,))
		});
		let sassafras_params = SassafrasWorkerParams {
			client: client.clone(),
			keystore,
			select_chain,
			env,
			block_import: data.block_import.clone(),
			sassafras_link: data.link.clone(),
			sync_oracle: DummyOracle,
			justification_sync_link: (),
			force_authoring: false,
			create_inherent_data_providers,
		};
		let sassafras_worker = start_sassafras(sassafras_params).unwrap();
		sassafras_workers.push(sassafras_worker);
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
		future::select(future::join_all(import_notifications), future::join_all(sassafras_workers)),
	));
}
