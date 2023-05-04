// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! BABE testsuite

use super::*;
use authorship::claim_slot;
use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
use sc_client_api::{backend::TransactionFor, BlockchainEvents, Finalizer};
use sc_consensus::{BoxBlockImport, BoxJustificationImport};
use sc_consensus_epochs::{EpochIdentifier, EpochIdentifierPosition};
use sc_consensus_slots::BackoffAuthoringOnFinalizedHeadLagging;
use sc_network_test::{Block as TestBlock, *};
use sp_application_crypto::key_types::BABE;
use sp_consensus::{DisableProofRecording, NoNetwork as DummyOracle, Proposal};
use sp_consensus_babe::{
	inherents::InherentDataProvider, make_vrf_sign_data, AllowedSlots, AuthorityId, AuthorityPair,
	Slot,
};
use sp_consensus_slots::SlotDuration;
use sp_core::crypto::Pair;
use sp_keyring::Sr25519Keyring;
use sp_keystore::{testing::MemoryKeystore, Keystore};
use sp_runtime::{
	generic::{Digest, DigestItem},
	traits::Block as BlockT,
};
use sp_timestamp::Timestamp;
use std::{cell::RefCell, task::Poll, time::Duration};

type Item = DigestItem;

type Error = sp_blockchain::Error;

type TestClient = substrate_test_runtime_client::client::Client<
	substrate_test_runtime_client::Backend,
	substrate_test_runtime_client::ExecutorDispatch,
	TestBlock,
	substrate_test_runtime_client::runtime::RuntimeApi,
>;

#[derive(Copy, Clone, PartialEq)]
enum Stage {
	PreSeal,
	PostSeal,
}

type Mutator = Arc<dyn Fn(&mut TestHeader, Stage) + Send + Sync>;

type BabeBlockImport =
	PanickingBlockImport<crate::BabeBlockImport<TestBlock, TestClient, Arc<TestClient>>>;

const SLOT_DURATION_MS: u64 = 1000;

#[derive(Clone)]
struct DummyFactory {
	client: Arc<TestClient>,
	epoch_changes: SharedEpochChanges<TestBlock, Epoch>,
	config: BabeConfiguration,
	mutator: Mutator,
}

struct DummyProposer {
	factory: DummyFactory,
	parent_hash: Hash,
	parent_number: u64,
	parent_slot: Slot,
}

impl Environment<TestBlock> for DummyFactory {
	type CreateProposer = future::Ready<Result<DummyProposer, Error>>;
	type Proposer = DummyProposer;
	type Error = Error;

	fn init(&mut self, parent_header: &<TestBlock as BlockT>::Header) -> Self::CreateProposer {
		let parent_slot = crate::find_pre_digest::<TestBlock>(parent_header)
			.expect("parent header has a pre-digest")
			.slot();

		future::ready(Ok(DummyProposer {
			factory: self.clone(),
			parent_hash: parent_header.hash(),
			parent_number: *parent_header.number(),
			parent_slot,
		}))
	}
}

impl DummyProposer {
	fn propose_with(
		&mut self,
		pre_digests: Digest,
	) -> future::Ready<
		Result<
			Proposal<
				TestBlock,
				sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>,
				(),
			>,
			Error,
		>,
	> {
		let block_builder =
			self.factory.client.new_block_at(self.parent_hash, pre_digests, false).unwrap();

		let mut block = match block_builder.build().map_err(|e| e.into()) {
			Ok(b) => b.block,
			Err(e) => return future::ready(Err(e)),
		};

		let this_slot = crate::find_pre_digest::<TestBlock>(block.header())
			.expect("baked block has valid pre-digest")
			.slot();

		// figure out if we should add a consensus digest, since the test runtime
		// doesn't.
		let epoch_changes = self.factory.epoch_changes.shared_data();
		let epoch = epoch_changes
			.epoch_data_for_child_of(
				descendent_query(&*self.factory.client),
				&self.parent_hash,
				self.parent_number,
				this_slot,
				|slot| Epoch::genesis(&self.factory.config, slot),
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
				authorities: epoch.authorities.clone(),
				randomness: epoch.randomness,
			})
			.encode();
			let digest = DigestItem::Consensus(BABE_ENGINE_ID, digest_data);
			block.header.digest_mut().push(digest)
		}

		// mutate the block header according to the mutator.
		(self.factory.mutator)(&mut block.header, Stage::PreSeal);

		future::ready(Ok(Proposal { block, proof: (), storage_changes: Default::default() }))
	}
}

impl Proposer<TestBlock> for DummyProposer {
	type Error = Error;
	type Transaction =
		sc_client_api::TransactionFor<substrate_test_runtime_client::Backend, TestBlock>;
	type Proposal = future::Ready<Result<Proposal<TestBlock, Self::Transaction, ()>, Error>>;
	type ProofRecording = DisableProofRecording;
	type Proof = ();

	fn propose(
		mut self,
		_: InherentData,
		pre_digests: Digest,
		_: Duration,
		_: Option<usize>,
	) -> Self::Proposal {
		self.propose_with(pre_digests)
	}
}

thread_local! {
	static MUTATOR: RefCell<Mutator> = RefCell::new(Arc::new(|_, _|()));
}

#[derive(Clone)]
pub struct PanickingBlockImport<B>(B);

#[async_trait::async_trait]
impl<B: BlockImport<TestBlock>> BlockImport<TestBlock> for PanickingBlockImport<B>
where
	B::Transaction: Send,
	B: Send,
{
	type Error = B::Error;
	type Transaction = B::Transaction;

	async fn import_block(
		&mut self,
		block: BlockImportParams<TestBlock, Self::Transaction>,
	) -> Result<ImportResult, Self::Error> {
		Ok(self.0.import_block(block).await.expect("importing block failed"))
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<TestBlock>,
	) -> Result<ImportResult, Self::Error> {
		Ok(self.0.check_block(block).await.expect("checking block failed"))
	}
}

type BabePeer = Peer<Option<PeerData>, BabeBlockImport>;

#[derive(Default)]
pub struct BabeTestNet {
	peers: Vec<BabePeer>,
}

type TestHeader = <TestBlock as BlockT>::Header;

type TestSelectChain =
	substrate_test_runtime_client::LongestChain<substrate_test_runtime_client::Backend, TestBlock>;

pub struct TestVerifier {
	inner: BabeVerifier<
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
	>,
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
	) -> Result<BlockImportParams<TestBlock, ()>, String> {
		// apply post-sealing mutations (i.e. stripping seal, if desired).
		(self.mutator)(&mut block.header, Stage::PostSeal);
		self.inner.verify(block).await
	}
}

pub struct PeerData {
	link: BabeLink<TestBlock>,
	block_import: Mutex<
		Option<
			BoxBlockImport<
				TestBlock,
				TransactionFor<substrate_test_runtime_client::Backend, TestBlock>,
			>,
		>,
	>,
}

impl TestNetFactory for BabeTestNet {
	type Verifier = TestVerifier;
	type PeerData = Option<PeerData>;
	type BlockImport = BabeBlockImport;

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

		let block_import = PanickingBlockImport(block_import);

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
		trace!(target: LOG_TARGET, "Creating a verifier");

		// ensure block import and verifier are linked correctly.
		let data = maybe_link
			.as_ref()
			.expect("babe link always provided to verifier instantiation");

		let (_, longest_chain) = TestClientBuilder::new().build_with_longest_chain();

		TestVerifier {
			inner: BabeVerifier {
				client: client.clone(),
				select_chain: longest_chain,
				create_inherent_data_providers: Box::new(|_, _| async {
					let slot = InherentDataProvider::from_timestamp_and_slot_duration(
						Timestamp::current(),
						SlotDuration::from_millis(SLOT_DURATION_MS),
					);
					Ok((slot,))
				}),
				config: data.link.config.clone(),
				epoch_changes: data.link.epoch_changes.clone(),
				telemetry: None,
			},
			mutator: MUTATOR.with(|m| m.borrow().clone()),
		}
	}

	fn peer(&mut self, i: usize) -> &mut BabePeer {
		trace!(target: LOG_TARGET, "Retrieving a peer");
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<BabePeer> {
		trace!(target: LOG_TARGET, "Retrieving peers");
		&self.peers
	}

	fn peers_mut(&mut self) -> &mut Vec<BabePeer> {
		trace!(target: "babe", "Retrieving peers, mutable");
		&mut self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<BabePeer>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}
}

#[tokio::test]
#[should_panic]
async fn rejects_empty_block() {
	sp_tracing::try_init_simple();
	let mut net = BabeTestNet::new(3);
	let block_builder = |builder: BlockBuilder<_, _, _>| builder.build().unwrap().block;
	net.mut_peers(|peer| {
		peer[0].generate_blocks(1, BlockOrigin::NetworkInitialSync, block_builder);
	})
}

fn create_keystore(authority: Sr25519Keyring) -> KeystorePtr {
	let keystore = MemoryKeystore::new();
	keystore
		.sr25519_generate_new(BABE, Some(&authority.to_seed()))
		.expect("Generates authority key");
	keystore.into()
}

async fn run_one_test(mutator: impl Fn(&mut TestHeader, Stage) + Send + Sync + 'static) {
	sp_tracing::try_init_simple();
	let mutator = Arc::new(mutator) as Mutator;

	MUTATOR.with(|m| *m.borrow_mut() = mutator.clone());

	let net = BabeTestNet::new(3);

	let peers = [Sr25519Keyring::Alice, Sr25519Keyring::Bob, Sr25519Keyring::Charlie];

	let net = Arc::new(Mutex::new(net));
	let mut import_notifications = Vec::new();
	let mut babe_futures = Vec::new();

	for (peer_id, auth_id) in peers.iter().enumerate() {
		let mut net = net.lock();
		let peer = net.peer(peer_id);
		let client = peer.client().as_client();
		let select_chain = peer.select_chain().expect("Full client has select_chain");

		let keystore = create_keystore(*auth_id);

		let mut got_own = false;
		let mut got_other = false;

		let data = peer.data.as_ref().expect("babe link set up during initialization");

		let environ = DummyFactory {
			client: client.clone(),
			config: data.link.config.clone(),
			epoch_changes: data.link.epoch_changes.clone(),
			mutator: mutator.clone(),
		};

		import_notifications.push(
			// run each future until we get one of our own blocks with number higher than 5
			// that was produced locally.
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

		let client_clone = client.clone();
		babe_futures.push(
			start_babe(BabeParams {
				block_import: data.block_import.lock().take().expect("import set up during init"),
				select_chain,
				client,
				env: environ,
				sync_oracle: DummyOracle,
				create_inherent_data_providers: Box::new(move |parent, _| {
					// Get the slot of the parent header and just increase this slot.
					//
					// Below we will running everything in one big future. If we would use
					// time based slot, it can happen that on babe instance imports a block from
					// another babe instance and then tries to build a block in the same slot making
					// this test fail.
					let parent_header = client_clone.header(parent).ok().flatten().unwrap();
					let slot = Slot::from(
						find_pre_digest::<TestBlock>(&parent_header).unwrap().slot() + 1,
					);

					async move { Ok((InherentDataProvider::new(slot),)) }
				}),
				force_authoring: false,
				backoff_authoring_blocks: Some(BackoffAuthoringOnFinalizedHeadLagging::default()),
				babe_link: data.link.clone(),
				keystore,
				justification_sync_link: (),
				block_proposal_slot_portion: SlotProportion::new(0.5),
				max_block_proposal_slot_portion: None,
				telemetry: None,
			})
			.expect("Starts babe"),
		);
	}
	future::select(
		futures::future::poll_fn(move |cx| {
			let mut net = net.lock();
			net.poll(cx);
			for p in net.peers() {
				for (h, e) in p.failed_verifications() {
					panic!("Verification failed for {:?}: {}", h, e);
				}
			}

			Poll::<()>::Pending
		}),
		future::select(future::join_all(import_notifications), future::join_all(babe_futures)),
	)
	.await;
}

#[tokio::test]
async fn authoring_blocks() {
	run_one_test(|_, _| ()).await;
}

#[tokio::test]
#[should_panic]
async fn rejects_missing_inherent_digest() {
	run_one_test(|header: &mut TestHeader, stage| {
		let v = std::mem::take(&mut header.digest_mut().logs);
		header.digest_mut().logs = v
			.into_iter()
			.filter(|v| stage == Stage::PostSeal || v.as_babe_pre_digest().is_none())
			.collect()
	})
	.await;
}

#[tokio::test]
#[should_panic]
async fn rejects_missing_seals() {
	run_one_test(|header: &mut TestHeader, stage| {
		let v = std::mem::take(&mut header.digest_mut().logs);
		header.digest_mut().logs = v
			.into_iter()
			.filter(|v| stage == Stage::PreSeal || v.as_babe_seal().is_none())
			.collect()
	})
	.await;
}

#[tokio::test]
#[should_panic]
async fn rejects_missing_consensus_digests() {
	run_one_test(|header: &mut TestHeader, stage| {
		let v = std::mem::take(&mut header.digest_mut().logs);
		header.digest_mut().logs = v
			.into_iter()
			.filter(|v| stage == Stage::PostSeal || v.as_next_epoch_descriptor().is_none())
			.collect()
	})
	.await;
}

#[test]
fn wrong_consensus_engine_id_rejected() {
	sp_tracing::try_init_simple();
	let sig = AuthorityPair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal([0; 4], sig.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_none())
}

#[test]
fn malformed_pre_digest_rejected() {
	sp_tracing::try_init_simple();
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, [0; 64].to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
}

#[test]
fn sig_is_not_pre_digest() {
	sp_tracing::try_init_simple();
	let sig = AuthorityPair::generate().0.sign(b"");
	let bad_seal: Item = DigestItem::Seal(BABE_ENGINE_ID, sig.to_vec());
	assert!(bad_seal.as_babe_pre_digest().is_none());
	assert!(bad_seal.as_babe_seal().is_some())
}

#[test]
fn claim_epoch_slots() {
	// We don't require the full claim information, thus as a shorter alias we're
	// going to use a simple integer value. Generally not verbose enough, but good enough
	// to be used within the narrow scope of a single test.
	// 0 -> None (i.e. unable to claim the slot),
	// 1 -> Primary
	// 2 -> Secondary
	// 3 -> Secondary with VRF
	const EPOCH_DURATION: u64 = 10;

	let authority = Sr25519Keyring::Alice;
	let keystore = create_keystore(authority);

	let mut epoch = Epoch {
		start_slot: 0.into(),
		authorities: vec![(authority.public().into(), 1)],
		randomness: [0; 32],
		epoch_index: 1,
		duration: EPOCH_DURATION,
		config: BabeEpochConfiguration {
			c: (3, 10),
			allowed_slots: AllowedSlots::PrimaryAndSecondaryPlainSlots,
		},
	};

	let claim_slot_wrap = |s, e| match claim_slot(Slot::from(s as u64), &e, &keystore) {
		None => 0,
		Some((PreDigest::Primary(_), _)) => 1,
		Some((PreDigest::SecondaryPlain(_), _)) => 2,
		Some((PreDigest::SecondaryVRF(_), _)) => 3,
	};

	// With secondary mechanism we should be able to claim all slots.
	let claims: Vec<_> = (0..EPOCH_DURATION)
		.into_iter()
		.map(|slot| claim_slot_wrap(slot, epoch.clone()))
		.collect();
	assert_eq!(claims, [1, 2, 2, 1, 2, 2, 2, 2, 2, 1]);

	// With secondary with VRF mechanism we should be able to claim all the slots.
	epoch.config.allowed_slots = AllowedSlots::PrimaryAndSecondaryVRFSlots;
	let claims: Vec<_> = (0..EPOCH_DURATION)
		.into_iter()
		.map(|slot| claim_slot_wrap(slot, epoch.clone()))
		.collect();
	assert_eq!(claims, [1, 3, 3, 1, 3, 3, 3, 3, 3, 1]);

	// Otherwise with only vrf-based primary slots we are able to claim a subset of the slots.
	epoch.config.allowed_slots = AllowedSlots::PrimarySlots;
	let claims: Vec<_> = (0..EPOCH_DURATION)
		.into_iter()
		.map(|slot| claim_slot_wrap(slot, epoch.clone()))
		.collect();
	assert_eq!(claims, [1, 0, 0, 1, 0, 0, 0, 0, 0, 1]);
}

#[test]
fn claim_vrf_check() {
	let authority = Sr25519Keyring::Alice;
	let keystore = create_keystore(authority);

	let public = authority.public();

	let epoch = Epoch {
		start_slot: 0.into(),
		authorities: vec![(public.into(), 1)],
		randomness: [0; 32],
		epoch_index: 1,
		duration: 10,
		config: BabeEpochConfiguration {
			c: (3, 10),
			allowed_slots: AllowedSlots::PrimaryAndSecondaryVRFSlots,
		},
	};

	// We leverage the predictability of claim types given a constant randomness.

	// We expect a Primary claim for slot 0

	let pre_digest = match claim_slot(0.into(), &epoch, &keystore).unwrap().0 {
		PreDigest::Primary(d) => d,
		v => panic!("Unexpected pre-digest variant {:?}", v),
	};
	let data = make_vrf_sign_data(&epoch.randomness.clone(), 0.into(), epoch.epoch_index);
	let sign = keystore.sr25519_vrf_sign(AuthorityId::ID, &public, &data).unwrap().unwrap();
	assert_eq!(pre_digest.vrf_signature.output, sign.output);

	// We expect a SecondaryVRF claim for slot 1
	let pre_digest = match claim_slot(1.into(), &epoch, &keystore).unwrap().0 {
		PreDigest::SecondaryVRF(d) => d,
		v => panic!("Unexpected pre-digest variant {:?}", v),
	};
	let data = make_vrf_sign_data(&epoch.randomness.clone(), 1.into(), epoch.epoch_index);
	let sign = keystore.sr25519_vrf_sign(AuthorityId::ID, &public, &data).unwrap().unwrap();
	assert_eq!(pre_digest.vrf_signature.output, sign.output);

	// Check that correct epoch index has been used if epochs are skipped (primary VRF)
	let slot = Slot::from(103);
	let claim = match claim_slot(slot, &epoch, &keystore).unwrap().0 {
		PreDigest::Primary(d) => d,
		v => panic!("Unexpected claim variant {:?}", v),
	};
	let fixed_epoch = epoch.clone_for_slot(slot);
	let data = make_vrf_sign_data(&epoch.randomness.clone(), slot, fixed_epoch.epoch_index);
	let sign = keystore.sr25519_vrf_sign(AuthorityId::ID, &public, &data).unwrap().unwrap();
	assert_eq!(fixed_epoch.epoch_index, 11);
	assert_eq!(claim.vrf_signature.output, sign.output);

	// Check that correct epoch index has been used if epochs are skipped (secondary VRF)
	let slot = Slot::from(100);
	let pre_digest = match claim_slot(slot, &epoch, &keystore).unwrap().0 {
		PreDigest::SecondaryVRF(d) => d,
		v => panic!("Unexpected claim variant {:?}", v),
	};
	let fixed_epoch = epoch.clone_for_slot(slot);
	let data = make_vrf_sign_data(&epoch.randomness.clone(), slot, fixed_epoch.epoch_index);
	let sign = keystore.sr25519_vrf_sign(AuthorityId::ID, &public, &data).unwrap().unwrap();
	assert_eq!(fixed_epoch.epoch_index, 11);
	assert_eq!(pre_digest.vrf_signature.output, sign.output);
}

// Propose and import a new BABE block on top of the given parent.
async fn propose_and_import_block<Transaction: Send + 'static>(
	parent: &TestHeader,
	slot: Option<Slot>,
	proposer_factory: &mut DummyFactory,
	block_import: &mut BoxBlockImport<TestBlock, Transaction>,
) -> Hash {
	let mut proposer = proposer_factory.init(parent).await.unwrap();

	let slot = slot.unwrap_or_else(|| {
		let parent_pre_digest = find_pre_digest::<TestBlock>(parent).unwrap();
		parent_pre_digest.slot() + 1
	});

	let pre_digest = sp_runtime::generic::Digest {
		logs: vec![Item::babe_pre_digest(PreDigest::SecondaryPlain(SecondaryPlainPreDigest {
			authority_index: 0,
			slot,
		}))],
	};

	let parent_hash = parent.hash();

	let mut block = proposer.propose_with(pre_digest).await.unwrap().block;

	let epoch_descriptor = proposer_factory
		.epoch_changes
		.shared_data()
		.epoch_descriptor_for_child_of(
			descendent_query(&*proposer_factory.client),
			&parent_hash,
			*parent.number(),
			slot,
		)
		.unwrap()
		.unwrap();

	let seal = {
		// sign the pre-sealed hash of the block and then
		// add it to a digest item.
		let pair = AuthorityPair::from_seed(&[1; 32]);
		let pre_hash = block.header.hash();
		let signature = pair.sign(pre_hash.as_ref());
		Item::babe_seal(signature)
	};

	let post_hash = {
		block.header.digest_mut().push(seal.clone());
		let h = block.header.hash();
		block.header.digest_mut().pop();
		h
	};

	let mut import = BlockImportParams::new(BlockOrigin::Own, block.header);
	import.post_digests.push(seal);
	import.body = Some(block.extrinsics);
	import
		.insert_intermediate(INTERMEDIATE_KEY, BabeIntermediate::<TestBlock> { epoch_descriptor });
	import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
	let import_result = block_import.import_block(import).await.unwrap();

	match import_result {
		ImportResult::Imported(_) => {},
		_ => panic!("expected block to be imported"),
	}

	post_hash
}

// Propose and import n valid BABE blocks that are built on top of the given parent.
// The proposer takes care of producing epoch change digests according to the epoch
// duration (which is set to 6 slots in the test runtime).
async fn propose_and_import_blocks<Transaction: Send + 'static>(
	client: &PeersFullClient,
	proposer_factory: &mut DummyFactory,
	block_import: &mut BoxBlockImport<TestBlock, Transaction>,
	parent_hash: Hash,
	n: usize,
) -> Vec<Hash> {
	let mut hashes = Vec::with_capacity(n);
	let mut parent_header = client.header(parent_hash).unwrap().unwrap();

	for _ in 0..n {
		let block_hash =
			propose_and_import_block(&parent_header, None, proposer_factory, block_import).await;
		hashes.push(block_hash);
		parent_header = client.header(block_hash).unwrap().unwrap();
	}

	hashes
}

#[tokio::test]
async fn importing_block_one_sets_genesis_epoch() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");
	let client = peer.client().as_client();

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let genesis_header = client.header(client.chain_info().genesis_hash).unwrap().unwrap();

	let block_hash = propose_and_import_block(
		&genesis_header,
		Some(999.into()),
		&mut proposer_factory,
		&mut block_import,
	)
	.await;

	let genesis_epoch = Epoch::genesis(&data.link.config, 999.into());

	let epoch_changes = data.link.epoch_changes.shared_data();
	let epoch_for_second_block = epoch_changes
		.epoch_data_for_child_of(descendent_query(&*client), &block_hash, 1, 1000.into(), |slot| {
			Epoch::genesis(&data.link.config, slot)
		})
		.unwrap()
		.unwrap();

	assert_eq!(epoch_for_second_block, genesis_epoch);
}

#[tokio::test]
async fn revert_prunes_epoch_changes_and_removes_weights() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let backend = peer.client().as_backend();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");
	let epoch_changes = data.link.epoch_changes.clone();

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	// Test scenario.
	// Information for epoch 19 is produced on three different forks at block #13.
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
	let canon = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		21,
	)
	.await;
	let fork1 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[0], 10)
			.await;
	let fork2 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[7], 10)
			.await;
	let fork3 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[11], 8)
			.await;

	// We should be tracking a total of 9 epochs in the fork tree
	assert_eq!(epoch_changes.shared_data().tree().iter().count(), 8);
	// And only one root
	assert_eq!(epoch_changes.shared_data().tree().roots().count(), 1);

	// Revert canon chain to block #10 (best(21) - 11)
	revert(client.clone(), backend, 11).expect("revert should work for baked test scenario");

	// Load and check epoch changes.

	let actual_nodes =
		aux_schema::load_epoch_changes::<Block, TestClient>(&*client, &data.link.config)
			.expect("load epoch changes")
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
			aux_schema::load_block_weight(&*client, hash).unwrap().is_some() == expected
		})
	};
	assert!(weight_data_check(&canon[..10], true));
	assert!(weight_data_check(&canon[10..], false));
	assert!(weight_data_check(&fork1, true));
	assert!(weight_data_check(&fork2, true));
	assert!(weight_data_check(&fork3, false));
}

#[tokio::test]
async fn revert_not_allowed_for_finalized() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let backend = peer.client().as_backend();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let canon = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		3,
	)
	.await;

	// Finalize best block
	client.finalize_block(canon[2], None, false).unwrap();

	// Revert canon chain to last finalized block
	revert(client.clone(), backend, 100).expect("revert should work for baked test scenario");

	let weight_data_check = |hashes: &[Hash], expected: bool| {
		hashes.iter().all(|hash| {
			aux_schema::load_block_weight(&*client, hash).unwrap().is_some() == expected
		})
	};
	assert!(weight_data_check(&canon, true));
}

#[tokio::test]
async fn importing_epoch_change_block_prunes_tree() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");
	let epoch_changes = data.link.epoch_changes.clone();

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	// This is the block tree that we're going to use in this test. Each node
	// represents an epoch change block, the epoch duration is 6 slots.
	//
	//    *---- F (#7)
	//   /                 *------ G (#19) - H (#25)
	//  /                 /
	// A (#1) - B (#7) - C (#13) - D (#19) - E (#25)
	//                              \
	//                               *------ I (#25)

	// Create and import the canon chain and keep track of fork blocks (A, C, D)
	// from the diagram above.
	let canon = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		30,
	)
	.await;

	// Create the forks
	let fork_1 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[0], 10)
			.await;
	let fork_2 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[12], 15)
			.await;
	let fork_3 =
		propose_and_import_blocks(&client, &mut proposer_factory, &mut block_import, canon[18], 10)
			.await;

	// We should be tracking a total of 9 epochs in the fork tree
	assert_eq!(epoch_changes.shared_data().tree().iter().count(), 9);

	// And only one root
	assert_eq!(epoch_changes.shared_data().tree().roots().count(), 1);

	// We finalize block #13 from the canon chain, so on the next epoch
	// change the tree should be pruned, to not contain F (#7).
	client.finalize_block(canon[12], None, false).unwrap();
	propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().best_hash,
		7,
	)
	.await;

	let nodes: Vec<_> = epoch_changes.shared_data().tree().iter().map(|(h, _, _)| *h).collect();

	// no hashes from the first fork must exist on the tree
	assert!(!nodes.iter().any(|h| fork_1.contains(h)));

	// but the epoch changes from the other forks must still exist
	assert!(nodes.iter().any(|h| fork_2.contains(h)));
	assert!(nodes.iter().any(|h| fork_3.contains(h)));

	// finalizing block #25 from the canon chain should prune out the second fork
	client.finalize_block(canon[24], None, false).unwrap();
	propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().best_hash,
		8,
	)
	.await;

	let nodes: Vec<_> = epoch_changes.shared_data().tree().iter().map(|(h, _, _)| *h).collect();

	// no hashes from the other forks must exist on the tree
	assert!(!nodes.iter().any(|h| fork_2.contains(h)));
	assert!(!nodes.iter().any(|h| fork_3.contains(h)));

	// Check that we contain the nodes that we care about
	assert!(nodes.iter().any(|h| *h == canon[18]));
	assert!(nodes.iter().any(|h| *h == canon[24]));
}

#[tokio::test]
#[should_panic]
async fn verify_slots_are_strictly_increasing() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let genesis_header = client.header(client.chain_info().genesis_hash).unwrap().unwrap();

	// we should have no issue importing this block
	let b1 = propose_and_import_block(
		&genesis_header,
		Some(999.into()),
		&mut proposer_factory,
		&mut block_import,
	)
	.await;

	let b1 = client.header(b1).unwrap().unwrap();

	// we should fail to import this block since the slot number didn't increase.
	// we will panic due to the `PanickingBlockImport` defined above.
	propose_and_import_block(&b1, Some(999.into()), &mut proposer_factory, &mut block_import).await;
}

#[tokio::test]
async fn obsolete_blocks_aux_data_cleanup() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");
	let client = peer.client().as_client();

	// Register the handler (as done by `babe_start`)
	let client_clone = client.clone();
	let on_finality = move |summary: &FinalityNotification<TestBlock>| {
		aux_storage_cleanup(client_clone.as_ref(), summary)
	};
	client.register_finality_action(Box::new(on_finality));

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let aux_data_check = |hashes: &[Hash], expected: bool| {
		hashes.iter().all(|hash| {
			aux_schema::load_block_weight(&*peer.client().as_backend(), hash)
				.unwrap()
				.is_some() == expected
		})
	};

	// Create the following test scenario:
	//
	//  /--- --B3 --- B4                       ( < fork2 )
	// G --- A1 --- A2 --- A3 --- A4           ( < fork1 )
	//                      \-----C4 --- C5    ( < fork3 )

	let fork1_hashes = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		4,
	)
	.await;
	let fork2_hashes = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		2,
	)
	.await;
	let fork3_hashes = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		fork1_hashes[2],
		2,
	)
	.await;

	// Check that aux data is present for all but the genesis block.
	assert!(aux_data_check(&[client.chain_info().genesis_hash], false));
	assert!(aux_data_check(&fork1_hashes, true));
	assert!(aux_data_check(&fork2_hashes, true));
	assert!(aux_data_check(&fork3_hashes, true));

	// Finalize A3
	client.finalize_block(fork1_hashes[2], None, true).unwrap();

	// Wiped: A1, A2
	assert!(aux_data_check(&fork1_hashes[..2], false));
	// Present: A3, A4
	assert!(aux_data_check(&fork1_hashes[2..], true));
	// Wiped: B3, B4
	assert!(aux_data_check(&fork2_hashes, false));
	// Present C4, C5
	assert!(aux_data_check(&fork3_hashes, true));

	client.finalize_block(fork1_hashes[3], None, true).unwrap();

	// Wiped: A3
	assert!(aux_data_check(&fork1_hashes[2..3], false));
	// Present: A4
	assert!(aux_data_check(&fork1_hashes[3..], true));
	// Present C4, C5
	assert!(aux_data_check(&fork3_hashes, true));
}

#[tokio::test]
async fn allows_skipping_epochs() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let epoch_changes = data.link.epoch_changes.clone();
	let epoch_length = data.link.config.epoch_length;

	// we create all of the blocks in epoch 0 as well as a block in epoch 1
	let blocks = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		epoch_length as usize + 1,
	)
	.await;

	// the first block in epoch 0 (#1) announces both epoch 0 and 1 (this is a
	// special genesis epoch)
	let epoch0 = epoch_changes
		.shared_data()
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Genesis0,
			hash: blocks[0],
			number: 1,
		})
		.unwrap()
		.clone();

	assert_eq!(epoch0.epoch_index, 0);
	assert_eq!(epoch0.start_slot, Slot::from(1));

	let epoch1 = epoch_changes
		.shared_data()
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Genesis1,
			hash: blocks[0],
			number: 1,
		})
		.unwrap()
		.clone();

	assert_eq!(epoch1.epoch_index, 1);
	assert_eq!(epoch1.start_slot, Slot::from(epoch_length + 1));

	// the first block in epoch 1 (#7) announces epoch 2. we will be skipping
	// this epoch and therefore re-using its data for epoch 3
	let epoch2 = epoch_changes
		.shared_data()
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: blocks[epoch_length as usize],
			number: epoch_length + 1,
		})
		.unwrap()
		.clone();

	assert_eq!(epoch2.epoch_index, 2);
	assert_eq!(epoch2.start_slot, Slot::from(epoch_length * 2 + 1));

	// we now author a block that belongs to epoch 3, thereby skipping epoch 2
	let last_block = client.expect_header(*blocks.last().unwrap()).unwrap();
	let block = propose_and_import_block(
		&last_block,
		Some((epoch_length * 3 + 1).into()),
		&mut proposer_factory,
		&mut block_import,
	)
	.await;

	// and the first block in epoch 3 (#8) announces epoch 4
	let epoch4 = epoch_changes
		.shared_data()
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: block,
			number: epoch_length + 2,
		})
		.unwrap()
		.clone();

	assert_eq!(epoch4.epoch_index, 4);
	assert_eq!(epoch4.start_slot, Slot::from(epoch_length * 4 + 1));

	// if we try to get the epoch data for a slot in epoch 3
	let epoch3 = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&block,
			epoch_length + 2,
			(epoch_length * 3 + 2).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	// we get back the data for epoch 2
	assert_eq!(epoch3, epoch2);

	// but if we try to get the epoch data for a slot in epoch 4
	let epoch4_ = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&block,
			epoch_length + 2,
			(epoch_length * 4 + 1).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	// we get epoch 4 as expected
	assert_eq!(epoch4, epoch4_);
}

#[tokio::test]
async fn allows_skipping_epochs_on_some_forks() {
	let mut net = BabeTestNet::new(1);

	let peer = net.peer(0);
	let data = peer.data.as_ref().expect("babe link set up during initialization");

	let client = peer.client().as_client();
	let mut block_import = data.block_import.lock().take().expect("import set up during init");

	let mut proposer_factory = DummyFactory {
		client: client.clone(),
		config: data.link.config.clone(),
		epoch_changes: data.link.epoch_changes.clone(),
		mutator: Arc::new(|_, _| ()),
	};

	let epoch_changes = data.link.epoch_changes.clone();
	let epoch_length = data.link.config.epoch_length;

	// we create all of the blocks in epoch 0 as well as two blocks in epoch 1
	let blocks = propose_and_import_blocks(
		&client,
		&mut proposer_factory,
		&mut block_import,
		client.chain_info().genesis_hash,
		epoch_length as usize + 1,
	)
	.await;

	// we now author a block that belongs to epoch 2, built on top of the last
	// authored block in epoch 1.
	let last_block = client.expect_header(*blocks.last().unwrap()).unwrap();

	let epoch2_block = propose_and_import_block(
		&last_block,
		Some((epoch_length * 2 + 1).into()),
		&mut proposer_factory,
		&mut block_import,
	)
	.await;

	// if we try to get the epoch data for a slot in epoch 2, we get the data that
	// was previously announced when epoch 1 started
	let epoch2 = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&epoch2_block,
			epoch_length + 2,
			(epoch_length * 2 + 2).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	// we now author a block that belongs to epoch 3, built on top of the last
	// authored block in epoch 1. authoring this block means we're skipping epoch 2
	// entirely on this fork
	let epoch3_block = propose_and_import_block(
		&last_block,
		Some((epoch_length * 3 + 1).into()),
		&mut proposer_factory,
		&mut block_import,
	)
	.await;

	// if we try to get the epoch data for a slot in epoch 3
	let epoch3_ = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&epoch3_block,
			epoch_length + 2,
			(epoch_length * 3 + 2).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	// we get back the data for epoch 2
	assert_eq!(epoch3_, epoch2);

	// if we try to get the epoch data for a slot in epoch 4 in the fork
	// where we skipped epoch 2, we should get the epoch data for epoch 4
	// that was announced at the beginning of epoch 3
	let epoch_data = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&epoch3_block,
			epoch_length + 2,
			(epoch_length * 4 + 1).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	assert!(epoch_data != epoch3_);

	// if we try to get the epoch data for a slot in epoch 4 in the fork
	// where we didn't skip epoch 2, we should get back the data for epoch 3,
	// that was announced when epoch 2 started in that fork
	let epoch_data = epoch_changes
		.shared_data()
		.epoch_data_for_child_of(
			descendent_query(&*client),
			&epoch2_block,
			epoch_length + 2,
			(epoch_length * 4 + 1).into(),
			|slot| Epoch::genesis(&data.link.config, slot),
		)
		.unwrap()
		.unwrap();

	assert!(epoch_data != epoch3_);

	let epoch3 = epoch_changes
		.shared_data()
		.epoch(&EpochIdentifier {
			position: EpochIdentifierPosition::Regular,
			hash: epoch2_block,
			number: epoch_length + 2,
		})
		.unwrap()
		.clone();

	assert_eq!(epoch_data, epoch3);
}
