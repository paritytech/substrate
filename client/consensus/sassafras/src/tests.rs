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

// TODO-SASS-P2
// Missing interesting tests:
// - verify block claimed via primary method

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
use sp_consensus_sassafras::{inherents::InherentDataProvider, vrf::make_slot_transcript_data};
use sp_keyring::Sr25519Keyring;
use sp_keystore::testing::KeyStore as TestKeyStore;
use sp_runtime::{Digest, DigestItem};
use sp_timestamp::Timestamp;

use substrate_test_runtime_client::{runtime::Block as TestBlock, Backend as TestBackend};

// Monomorphization of generic structures for the test context.

type BlockId = crate::BlockId<TestBlock>;

type TestHeader = <TestBlock as BlockT>::Header;

type TestClient = substrate_test_runtime_client::client::Client<
	TestBackend,
	substrate_test_runtime_client::ExecutorDispatch,
	TestBlock,
	substrate_test_runtime_client::runtime::RuntimeApi,
>;

type TestSelectChain =
	substrate_test_runtime_client::LongestChain<substrate_test_runtime_client::Backend, TestBlock>;

type TestTransaction =
	sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>;

type TestBlockImportParams = BlockImportParams<TestBlock, TestTransaction>;

type TestViableEpochDescriptor = sc_consensus_epochs::ViableEpochDescriptor<Hash, u64, Epoch>;

// Monomorphization of Sassafras structures for the test context.

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

// Epoch duration is slots
const EPOCH_DURATION: u64 = 6;
// Slot duration is milliseconds
const SLOT_DURATION: u64 = 1000;

struct TestProposer {
	client: Arc<TestClient>,
	link: SassafrasLink,
	parent_hash: Hash,
	parent_number: u64,
	parent_slot: Slot,
}

impl TestProposer {
	fn propose_block(self, digest: Digest) -> TestBlock {
		block_on(self.propose(InherentData::default(), digest, Duration::default(), None))
			.expect("Proposing block")
			.block
	}
}

impl Proposer<TestBlock> for TestProposer {
	type Error = TestError;
	type Transaction = TestTransaction;
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

		let epoch_changes = self.link.epoch_changes.shared_data();
		let epoch = epoch_changes
			.epoch_data_for_child_of(
				descendent_query(&*self.client),
				&self.parent_hash,
				self.parent_number,
				this_slot,
				|slot| Epoch::genesis(&self.link.genesis_config, slot),
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

struct TestContext {
	client: Arc<TestClient>,
	backend: Arc<TestBackend>,
	link: SassafrasLink,
	block_import: SassafrasBlockImport,
	verifier: SassafrasVerifier,
}

fn create_test_verifier(
	client: Arc<TestClient>,
	link: &SassafrasLink,
	config: SassafrasConfiguration,
) -> SassafrasVerifier {
	let slot_duration = config.slot_duration();

	let create_inherent_data_providers = Box::new(move |_, _| async move {
		let slot = InherentDataProvider::from_timestamp_and_slot_duration(
			Timestamp::current(),
			slot_duration,
		);
		Ok((slot,))
	});

	let (_, longest_chain) = TestClientBuilder::with_default_backend().build_with_longest_chain();

	SassafrasVerifier::new(
		client.clone(),
		longest_chain,
		create_inherent_data_providers,
		link.epoch_changes.clone(),
		None,
		config,
	)
}

fn create_test_block_import(
	client: Arc<TestClient>,
	config: SassafrasConfiguration,
) -> (SassafrasBlockImport, SassafrasLink) {
	crate::block_import(config, client.clone(), client.clone())
		.expect("can initialize block-import")
}

impl TestContext {
	fn new() -> Self {
		let (client, backend) = TestClientBuilder::with_default_backend().build_with_backend();
		let client = Arc::new(client);

		// Note: configuration is loaded using the `TestClient` instance as the runtime-api
		// provider. In practice this will use the values defined within the test runtime
		// defined in the `substrate_test_runtime` crate.
		let config = crate::configuration(&*client).expect("config available");

		let (block_import, link) = create_test_block_import(client.clone(), config.clone());

		let verifier = create_test_verifier(client.clone(), &link, config.clone());

		Self { client, backend, link, block_import, verifier }
	}

	// This is a bit hacky solution to use `TestContext` as an `Environment` implementation
	fn new_with_pre_built_data(
		client: Arc<TestClient>,
		backend: Arc<TestBackend>,
		link: SassafrasLink,
		block_import: SassafrasBlockImport,
	) -> Self {
		let verifier = create_test_verifier(client.clone(), &link, link.genesis_config.clone());
		Self { client, backend, link, block_import, verifier }
	}

	fn import_block(&mut self, mut params: TestBlockImportParams) -> Hash {
		let post_hash = params.post_hash();

		if params.post_digests.is_empty() {
			// Assume that the seal has not been removed yet. Remove it here...
			// NOTE: digest may be empty because of some test intentionally clearing up
			// the whole digest logs.
			if let Some(seal) = params.header.digest_mut().pop() {
				params.post_digests.push(seal);
			}
		}

		match block_on(self.block_import.import_block(params, Default::default())).unwrap() {
			ImportResult::Imported(_) => (),
			_ => panic!("expected block to be imported"),
		}

		post_hash
	}

	fn verify_block(&mut self, params: TestBlockImportParams) -> TestBlockImportParams {
		let tmp_params = params.clear_storage_changes_and_mutate();
		let (tmp_params, _) = block_on(self.verifier.verify(tmp_params)).unwrap();
		tmp_params.clear_storage_changes_and_mutate()
	}

	fn epoch_data(&self, parent_hash: &Hash, parent_number: u64, slot: Slot) -> Epoch {
		self.link
			.epoch_changes
			.shared_data()
			.epoch_data_for_child_of(
				descendent_query(&*self.client),
				&parent_hash,
				parent_number,
				slot,
				|slot| Epoch::genesis(&self.link.genesis_config, slot),
			)
			.unwrap()
			.unwrap()
	}

	fn epoch_descriptor(
		&self,
		parent_hash: &Hash,
		parent_number: u64,
		slot: Slot,
	) -> TestViableEpochDescriptor {
		self.link
			.epoch_changes
			.shared_data()
			.epoch_descriptor_for_child_of(
				descendent_query(&*self.client),
				&parent_hash,
				parent_number,
				slot,
			)
			.unwrap()
			.unwrap()
	}

	// Propose a block
	fn propose_block(&mut self, parent_hash: Hash, slot: Option<Slot>) -> TestBlockImportParams {
		let parent_header = self.client.header(parent_hash).unwrap().unwrap();
		let parent_number = *parent_header.number();

		let authority = Sr25519Keyring::Alice;
		let keystore = create_keystore(authority);

		let proposer = block_on(self.init(&parent_header)).unwrap();

		let slot = slot.unwrap_or_else(|| {
			let parent_pre_digest = find_pre_digest::<TestBlock>(&parent_header).unwrap();
			parent_pre_digest.slot + 1
		});

		let epoch = self.epoch_data(&parent_hash, parent_number, slot);
		let transcript_data =
			make_slot_transcript_data(&self.link.genesis_config.randomness, slot, epoch.epoch_idx);
		let signature = SyncCryptoStore::sr25519_vrf_sign(
			&*keystore,
			SASSAFRAS,
			&authority.public(),
			transcript_data,
		)
		.unwrap()
		.unwrap();

		let pre_digest = PreDigest {
			slot,
			authority_idx: 0,
			vrf_output: VRFOutput(signature.output),
			vrf_proof: VRFProof(signature.proof),
			ticket_aux: None,
		};
		let digest = sp_runtime::generic::Digest {
			logs: vec![DigestItem::sassafras_pre_digest(pre_digest)],
		};

		let mut block = proposer.propose_block(digest);

		let epoch_descriptor = self.epoch_descriptor(&parent_hash, parent_number, slot);

		// Sign the pre-sealed hash of the block and then add it to a digest item.
		let hash = block.header.hash();
		let public_type_pair = authority.public().into();
		let signature =
			SyncCryptoStore::sign_with(&*keystore, SASSAFRAS, &public_type_pair, hash.as_ref())
				.unwrap()
				.unwrap()
				.try_into()
				.unwrap();
		let seal = DigestItem::sassafras_seal(signature);
		block.header.digest_mut().push(seal);

		let mut params = BlockImportParams::new(BlockOrigin::Own, block.header);
		params.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		params.body = Some(block.extrinsics);
		params.insert_intermediate(INTERMEDIATE_KEY, SassafrasIntermediate { epoch_descriptor });

		params
	}

	// Propose and import a new block on top of the given parent.
	// This skips verification.
	fn propose_and_import_block(&mut self, parent_hash: Hash, slot: Option<Slot>) -> Hash {
		let params = self.propose_block(parent_hash, slot);
		self.import_block(params)
	}

	// Propose and import n valid blocks that are built on top of the given parent.
	// The proposer takes care of producing epoch change digests according to the epoch
	// duration (which is set by the test runtime).
	fn propose_and_import_blocks(&mut self, mut parent_hash: Hash, n: usize) -> Vec<Hash> {
		let mut hashes = Vec::with_capacity(n);
		for _ in 0..n {
			let hash = self.propose_and_import_block(parent_hash, None);
			hashes.push(hash);
			parent_hash = hash;
		}
		hashes
	}
}

fn create_keystore(authority: Sr25519Keyring) -> SyncCryptoStorePtr {
	let keystore = Arc::new(TestKeyStore::new());
	SyncCryptoStore::sr25519_generate_new(&*keystore, SASSAFRAS, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore
}

#[test]
fn tests_assumptions_sanity_check() {
	let env = TestContext::new();
	let config = env.link.genesis_config;

	// Check that genesis configuration read from test runtime has the expected values
	assert_eq!(
		config.authorities,
		vec![
			(Sr25519Keyring::Alice.public().into(), 1),
			(Sr25519Keyring::Bob.public().into(), 1),
			(Sr25519Keyring::Charlie.public().into(), 1),
		]
	);
	assert_eq!(config.epoch_duration, EPOCH_DURATION);
	assert_eq!(config.slot_duration, SLOT_DURATION);
	assert_eq!(config.randomness, [0; 32]);
	// TODO-SASS-P3: check threshold params
}

#[test]
fn claim_secondary_slots_works() {
	let env = TestContext::new();
	let mut config = env.link.genesis_config.clone();
	config.randomness = [2; 32];

	let authorities = [Sr25519Keyring::Alice, Sr25519Keyring::Bob, Sr25519Keyring::Charlie];

	let epoch = Epoch {
		epoch_idx: 1,
		start_slot: 6.into(),
		config: config.clone(),
		tickets_aux: Default::default(),
	};

	let mut assignments = vec![usize::MAX; config.epoch_duration as usize];

	for (auth_idx, auth_id) in authorities.iter().enumerate() {
		let keystore = create_keystore(*auth_id);

		for slot in 0..config.epoch_duration {
			if let Some((claim, auth_id2)) =
				authorship::claim_slot(slot.into(), &epoch, None, &keystore)
			{
				assert_eq!(claim.authority_idx as usize, auth_idx);
				assert_eq!(claim.slot, Slot::from(slot));
				assert_eq!(claim.ticket_aux, None);
				assert_eq!(auth_id.public(), auth_id2.into());

				// Check that this slot has not been assigned before
				assert_eq!(assignments[slot as usize], usize::MAX);
				assignments[slot as usize] = auth_idx;
			}
		}
	}
	// Check that every slot has been assigned
	assert!(assignments.iter().all(|v| *v != usize::MAX));
	println!("secondary slots assignments: {:?}", assignments);
}

#[test]
fn claim_primary_slots_works() {
	// Here the test is very deterministic.
	// If a node has in its epoch `tickets_aux` the information corresponding to the
	// ticket that is presented. Then the claim ticket should just return the
	// ticket auxiliary information.
	let env = TestContext::new();
	let mut config = env.link.genesis_config.clone();
	config.randomness = [2; 32];

	let mut epoch = Epoch {
		epoch_idx: 1,
		start_slot: 6.into(),
		config: config.clone(),
		tickets_aux: Default::default(),
	};

	let keystore = create_keystore(Sr25519Keyring::Alice);

	// Success if we have ticket data and the key in our keystore

	let authority_idx = 0u32;
	let ticket: Ticket = [0u8; 32].try_into().unwrap();
	let ticket_proof: VRFProof = [0u8; 64].try_into().unwrap();
	let ticket_aux = TicketAux { attempt: 0, proof: ticket_proof };
	epoch.tickets_aux.insert(ticket, (authority_idx, ticket_aux));

	let (pre_digest, auth_id) =
		authorship::claim_slot(0.into(), &epoch, Some(ticket), &keystore).unwrap();

	assert_eq!(pre_digest.authority_idx, authority_idx);
	assert_eq!(auth_id, Sr25519Keyring::Alice.public().into());

	// Fail if we don't have aux data for some ticket

	let ticket: Ticket = [1u8; 32].try_into().unwrap();
	let claim = authorship::claim_slot(0.into(), &epoch, Some(ticket), &keystore);
	assert!(claim.is_none());

	// Fail if we don't have the key for the ticket owner in our keystore
	// (even though we have associated data, it doesn't matter)

	let authority_idx = 1u32;
	let ticket_proof: VRFProof = [0u8; 64].try_into().unwrap();
	let ticket_aux = TicketAux { attempt: 0, proof: ticket_proof };
	epoch.tickets_aux.insert(ticket, (authority_idx, ticket_aux));
	let claim = authorship::claim_slot(0.into(), &epoch, Some(ticket), &keystore);
	assert!(claim.is_none());
}

#[test]
#[should_panic(expected = "valid headers contain a pre-digest")]
fn import_rejects_block_without_pre_digest() {
	let mut env = TestContext::new();

	let mut import_params = env.propose_block(env.client.info().genesis_hash, Some(999.into()));
	// Remove logs from the header
	import_params.header.digest_mut().logs.clear();

	env.import_block(import_params);
}

#[test]
#[should_panic(expected = "Unexpected epoch change")]
fn import_rejects_block_with_unexpected_epoch_changes() {
	let mut env = TestContext::new();

	let hash1 = env.propose_and_import_block(env.client.info().genesis_hash, None);

	let mut import_params = env.propose_block(hash1, None);
	// Insert an epoch change announcement when it is not required.
	let digest_data = ConsensusLog::NextEpochData(NextEpochDescriptor {
		authorities: env.link.genesis_config.authorities.clone(),
		randomness: env.link.genesis_config.randomness,
		config: None,
	})
	.encode();
	let digest_item = DigestItem::Consensus(SASSAFRAS_ENGINE_ID, digest_data);
	let digest = import_params.header.digest_mut();
	digest.logs.insert(digest.logs.len() - 1, digest_item);

	env.import_block(import_params);
}

#[test]
#[should_panic(expected = "Expected epoch change to happen")]
fn import_rejects_block_with_missing_epoch_changes() {
	let mut env = TestContext::new();

	let blocks =
		env.propose_and_import_blocks(env.client.info().genesis_hash, EPOCH_DURATION as usize);

	let mut import_params = env.propose_block(blocks[EPOCH_DURATION as usize - 1], None);

	let digest = import_params.header.digest_mut();
	// Remove the epoch change announcement.
	// (Implementation detail: should be the second to last entry, just before the seal)
	digest.logs.remove(digest.logs.len() - 2);

	env.import_block(import_params);
}

#[test]
fn importing_block_one_sets_genesis_epoch() {
	let mut env = TestContext::new();

	let block_hash = env.propose_and_import_block(env.client.info().genesis_hash, Some(999.into()));

	let epoch_for_second_block = env.epoch_data(&block_hash, 1, 1000.into());
	let genesis_epoch = Epoch::genesis(&env.link.genesis_config, 999.into());
	assert_eq!(epoch_for_second_block, genesis_epoch);
}

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
	let mut env = TestContext::new();

	let blocks = env.propose_and_import_blocks(env.client.info().genesis_hash, 7);

	// First block after the a skipped epoch (block #8 @ slot #19)
	let block = env.propose_and_import_block(*blocks.last().unwrap(), Some(19.into()));

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
	assert_eq!(data.epoch_idx, 0);
	assert_eq!(data.start_slot, Slot::from(1));

	// First block in E0 (B1) also announces E1
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Genesis1,
			hash: blocks[0],
			number: 1,
		})
		.unwrap();
	assert_eq!(data.epoch_idx, 1);
	assert_eq!(data.start_slot, Slot::from(7));

	// First block in E1 (B7) announces E2
	// NOTE: config is used by E3 without altering epoch node values.
	// This will break as soon as our assumptions about how fork-tree traversal works
	// are not met anymore (this is a good thing)
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: blocks[6],
			number: 7,
		})
		.unwrap();
	assert_eq!(data.epoch_idx, 2);
	assert_eq!(data.start_slot, Slot::from(13));

	// First block in E3 (B8) announced E4.
	let data = epoch_changes
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: block,
			number: 8,
		})
		.unwrap();
	assert_eq!(data.epoch_idx, 4);
	assert_eq!(data.start_slot, Slot::from(25));
}

#[test]
fn finalization_prunes_epoch_changes_and_removes_weights() {
	let mut env = TestContext::new();

	let canon = env.propose_and_import_blocks(env.client.info().genesis_hash, 21);

	let _fork1 = env.propose_and_import_blocks(canon[0], 10);
	let _fork2 = env.propose_and_import_blocks(canon[7], 10);
	let _fork3 = env.propose_and_import_blocks(canon[11], 8);

	let epoch_changes = env.link.epoch_changes.clone();

	// We should be tracking a total of 9 epochs in the fork tree
	assert_eq!(epoch_changes.shared_data().tree().iter().count(), 8);
	// And only one root
	assert_eq!(epoch_changes.shared_data().tree().roots().count(), 1);

	// Pre-finalize scenario.
	//
	// X(#y): a block (number y) announcing the next epoch data.
	// Information for epoch starting at block #19 is produced on three different forks
	// at block #13.
	//
	// Finalize block #14
	//
	//                        *---------------- F(#13) --#18                  < fork #2
	//                       /
	// A(#1) ---- B(#7) ----#8----------#12---- C(#13) ---- D(#19) ------#21  < canon
	//   \                                \
	//    \                               *---- G(#13) ---- H(#19) ---#20     < fork #3
	//     \
	//      *-----E(#7)---#11                                          		  < fork #1

	// Finalize block #10 so that on next epoch change the tree is pruned
	env.client.finalize_block(canon[13], None, true).unwrap();
	let canon_tail = env.propose_and_import_blocks(*canon.last().unwrap(), 4);

	// Post-finalize scenario.
	//
	// B(#7)------ C(#13) ---- D(#19) ------Z(#25)

	let epoch_changes = epoch_changes.shared_data();
	let epoch_changes: Vec<_> = epoch_changes.tree().iter().map(|(h, _, _)| *h).collect();

	assert_eq!(epoch_changes, vec![canon[6], canon[12], canon[18], canon_tail[3]]);

	// TODO-SASS-P3
	//todo!("Requires aux_storage_cleanup");
}

#[test]
fn revert_prunes_epoch_changes_and_removes_weights() {
	let mut env = TestContext::new();

	let canon = env.propose_and_import_blocks(env.client.info().genesis_hash, 21);
	let fork1 = env.propose_and_import_blocks(canon[0], 10);
	let fork2 = env.propose_and_import_blocks(canon[7], 10);
	let fork3 = env.propose_and_import_blocks(canon[11], 8);

	let epoch_changes = env.link.epoch_changes.clone();

	// We should be tracking a total of 9 epochs in the fork tree
	assert_eq!(epoch_changes.shared_data().tree().iter().count(), 8);
	// And only one root
	assert_eq!(epoch_changes.shared_data().tree().roots().count(), 1);

	// Pre-revert scenario.
	//
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
	//      *-----E(#7)---#11                                          		   < fork #1

	// Revert canon chain to block #10 (best(21) - 11)
	crate::revert(env.backend.clone(), 11).unwrap();

	// Post-revert expected scenario.
	//
	//
	//                        *----------------- F(#13) --#18
	//                       /
	// A(#1) ---- B(#7) ----#8----#10
	//   \
	//    *------ E(#7)---#11

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
	let mut env = TestContext::new();

	let canon = env.propose_and_import_blocks(env.client.info().genesis_hash, 3);

	// Finalize best block
	env.client.finalize_block(canon[2], None, false).unwrap();

	// Revert canon chain to last finalized block
	crate::revert(env.backend.clone(), 100).expect("revert should work for baked test scenario");

	let weight_data_check = |hashes: &[Hash], expected: bool| {
		hashes.iter().all(|hash| {
			aux_schema::load_block_weight(&*env.client, hash).unwrap().is_some() == expected
		})
	};
	assert!(weight_data_check(&canon, true));
}

#[test]
fn verify_block_claimed_via_secondary_method() {
	let mut env = TestContext::new();

	let blocks = env.propose_and_import_blocks(env.client.info().genesis_hash, 7);

	let in_params = env.propose_block(blocks[6], Some(9.into()));

	let _out_params = env.verify_block(in_params);
}

//=================================================================================================
// More complex tests involving communication between multiple nodes.
//
// These tests are performed via a specially crafted test network.
//=================================================================================================

impl Environment<TestBlock> for TestContext {
	type CreateProposer = future::Ready<Result<TestProposer, TestError>>;
	type Proposer = TestProposer;
	type Error = TestError;

	fn init(&mut self, parent_header: &TestHeader) -> Self::CreateProposer {
		let parent_slot = crate::find_pre_digest::<TestBlock>(parent_header)
			.expect("parent header has a pre-digest")
			.slot;

		future::ready(Ok(TestProposer {
			client: self.client.clone(),
			link: self.link.clone(),
			parent_hash: parent_header.hash(),
			parent_number: *parent_header.number(),
			parent_slot,
		}))
	}
}

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
		let (block_import, link) = create_test_block_import(client.clone(), config);

		(BlockImportAdapter::new(block_import.clone()), None, Some(PeerData { link, block_import }))
	}

	fn make_verifier(&self, client: PeersClient, maybe_link: &Option<PeerData>) -> Self::Verifier {
		let client = client.as_client();

		let data = maybe_link.as_ref().expect("data provided to verifier instantiation");

		let config = crate::configuration(&*client).expect("config available");
		create_test_verifier(client.clone(), &data.link, config)
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
#[tokio::test]
async fn sassafras_network_progress() {
	let net = SassafrasTestNet::new(3);
	let net = Arc::new(Mutex::new(net));

	let peers = [Sr25519Keyring::Alice, Sr25519Keyring::Bob, Sr25519Keyring::Charlie];

	let mut import_notifications = Vec::new();
	let mut sassafras_workers = Vec::new();

	for (peer_id, auth_id) in peers.iter().enumerate() {
		let mut net = net.lock();
		let peer = net.peer(peer_id);
		let client = peer.client().as_client();
		let backend = peer.client().as_backend();
		let select_chain = peer.select_chain().expect("Full client has select_chain");

		let keystore = create_keystore(*auth_id);

		let data = peer.data.as_ref().expect("sassafras link set up during initialization");

		let env = TestContext::new_with_pre_built_data(
			client.clone(),
			backend.clone(),
			data.link.clone(),
			data.block_import.clone(),
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

		//let slot_duration = data.link.genesis_config.slot_duration();
		let client_clone = client.clone();
		let create_inherent_data_providers = Box::new(move |parent, _| {
			// Get the slot of the parent header and just increase this slot.
			//
			// Below we will running everything in one big future. If we would use
			// time based slot, it can happen that on babe instance imports a block from
			// another babe instance and then tries to build a block in the same slot making
			// this test fail.
			let parent_header = client_clone.header(parent).ok().flatten().unwrap();
			let slot = Slot::from(find_pre_digest::<TestBlock>(&parent_header).unwrap().slot + 1);
			async move { Ok((InherentDataProvider::new(slot),)) }
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

	future::select(
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
	)
	.await;
}
