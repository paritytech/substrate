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

//! Tests and test helpers for GRANDPA.

use super::*;
use assert_matches::assert_matches;
use async_trait::async_trait;
use environment::HasVoted;
use futures_timer::Delay;
use parking_lot::{Mutex, RwLock};
use sc_consensus::{
	BlockImport, BlockImportParams, BoxJustificationImport, ForkChoiceStrategy, ImportResult,
	ImportedAux,
};
use sc_network::config::Role;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, Hash, PassThroughVerifier, Peer, PeersClient,
	PeersFullClient, TestClient, TestNetFactory,
};
use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_consensus::{BlockOrigin, Error as ConsensusError, SelectChain};
use sp_consensus_grandpa::{
	AuthorityList, EquivocationProof, GrandpaApi, OpaqueKeyOwnershipProof, GRANDPA_ENGINE_ID,
};
use sp_core::H256;
use sp_keyring::Ed25519Keyring;
use sp_keystore::{testing::MemoryKeystore, Keystore, KeystorePtr};
use sp_runtime::{
	codec::Encode,
	generic::{BlockId, DigestItem},
	traits::{Block as BlockT, Header as HeaderT},
	Justifications,
};
use std::{collections::HashSet, pin::Pin};
use substrate_test_runtime_client::{runtime::BlockNumber, BlockBuilderExt};
use tokio::runtime::Handle;

use authorities::AuthoritySet;
use communication::grandpa_protocol_name;
use sc_block_builder::{BlockBuilder, BlockBuilderProvider};
use sc_consensus::LongestChain;
use sp_application_crypto::key_types::GRANDPA;

type TestLinkHalf =
	LinkHalf<Block, PeersFullClient, LongestChain<substrate_test_runtime_client::Backend, Block>>;
type PeerData = Mutex<Option<TestLinkHalf>>;
type GrandpaPeer = Peer<PeerData, GrandpaBlockImport>;
type GrandpaBlockImport = crate::GrandpaBlockImport<
	substrate_test_runtime_client::Backend,
	Block,
	PeersFullClient,
	LongestChain<substrate_test_runtime_client::Backend, Block>,
>;

#[derive(Default)]
struct GrandpaTestNet {
	peers: Vec<GrandpaPeer>,
	test_config: TestApi,
}

impl GrandpaTestNet {
	fn new(test_config: TestApi, n_authority: usize, n_full: usize) -> Self {
		let mut net =
			GrandpaTestNet { peers: Vec::with_capacity(n_authority + n_full), test_config };

		for _ in 0..n_authority {
			net.add_authority_peer();
		}

		for _ in 0..n_full {
			net.add_full_peer();
		}

		net
	}
}

impl GrandpaTestNet {
	fn add_authority_peer(&mut self) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![grandpa_protocol_name::NAME.into()],
			is_authority: true,
			..Default::default()
		})
	}
}

impl TestNetFactory for GrandpaTestNet {
	type Verifier = PassThroughVerifier;
	type PeerData = PeerData;
	type BlockImport = GrandpaBlockImport;

	fn add_full_peer(&mut self) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![grandpa_protocol_name::NAME.into()],
			is_authority: false,
			..Default::default()
		})
	}

	fn make_verifier(&self, _client: PeersClient, _: &PeerData) -> Self::Verifier {
		PassThroughVerifier::new(false) // use non-instant finality.
	}

	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (BlockImportAdapter<Self::BlockImport>, Option<BoxJustificationImport<Block>>, PeerData) {
		let (client, backend) = (client.as_client(), client.as_backend());
		let (import, link) = block_import(
			client.clone(),
			&self.test_config,
			LongestChain::new(backend.clone()),
			None,
		)
		.expect("Could not create block import for fresh peer.");
		let justification_import = Box::new(import.clone());
		(BlockImportAdapter::new(import), Some(justification_import), Mutex::new(Some(link)))
	}

	fn peer(&mut self, i: usize) -> &mut GrandpaPeer {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<GrandpaPeer> {
		&self.peers
	}

	fn peers_mut(&mut self) -> &mut Vec<GrandpaPeer> {
		&mut self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<GrandpaPeer>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}
}

#[derive(Default, Clone)]
pub(crate) struct TestApi {
	genesis_authorities: AuthorityList,
}

impl TestApi {
	pub fn new(genesis_authorities: AuthorityList) -> Self {
		TestApi { genesis_authorities }
	}
}

pub(crate) struct RuntimeApi {
	inner: TestApi,
}

impl ProvideRuntimeApi<Block> for TestApi {
	type Api = RuntimeApi;

	fn runtime_api(&self) -> ApiRef<'_, Self::Api> {
		RuntimeApi { inner: self.clone() }.into()
	}
}

sp_api::mock_impl_runtime_apis! {
	impl GrandpaApi<Block> for RuntimeApi {
		fn grandpa_authorities(&self) -> AuthorityList {
			self.inner.genesis_authorities.clone()
		}

		fn current_set_id(&self) -> SetId {
			0
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			_equivocation_proof: EquivocationProof<Hash, BlockNumber>,
			_key_owner_proof: OpaqueKeyOwnershipProof,
		) -> Option<()> {
			None
		}

		fn generate_key_ownership_proof(
			_set_id: SetId,
			_authority_id: AuthorityId,
		) -> Option<OpaqueKeyOwnershipProof> {
			None
		}
	}
}

impl GenesisAuthoritySetProvider<Block> for TestApi {
	fn get(&self) -> sp_blockchain::Result<AuthorityList> {
		Ok(self.genesis_authorities.clone())
	}
}

/// A mock `SelectChain` that allows the user to set the return values for each
/// method. After the `SelectChain` methods are called the pending value is
/// discarded and another call to set new values must be performed.
#[derive(Clone, Default)]
struct MockSelectChain {
	leaves: Arc<Mutex<Option<Vec<Hash>>>>,
	best_chain: Arc<Mutex<Option<<Block as BlockT>::Header>>>,
	finality_target: Arc<Mutex<Option<Hash>>>,
}

impl MockSelectChain {
	fn set_best_chain(&self, best: <Block as BlockT>::Header) {
		*self.best_chain.lock() = Some(best);
	}

	fn set_finality_target(&self, target: Hash) {
		*self.finality_target.lock() = Some(target);
	}
}

#[async_trait]
impl SelectChain<Block> for MockSelectChain {
	async fn leaves(&self) -> Result<Vec<Hash>, ConsensusError> {
		Ok(self.leaves.lock().take().unwrap())
	}

	async fn best_chain(&self) -> Result<<Block as BlockT>::Header, ConsensusError> {
		Ok(self.best_chain.lock().take().unwrap())
	}

	async fn finality_target(
		&self,
		_base_hash: Hash,
		_maybe_max_number: Option<NumberFor<Block>>,
	) -> Result<Hash, ConsensusError> {
		Ok(self.finality_target.lock().take().unwrap())
	}
}

// A mock voting rule that allows asserting an expected value for best block
#[derive(Clone, Default)]
struct AssertBestBlock(Arc<Mutex<Option<Hash>>>);

impl<B> VotingRule<Block, B> for AssertBestBlock
where
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		_backend: Arc<B>,
		_base: &<Block as BlockT>::Header,
		best_target: &<Block as BlockT>::Header,
		_current_target: &<Block as BlockT>::Header,
	) -> VotingRuleResult<Block> {
		if let Some(expected) = *self.0.lock() {
			assert_eq!(best_target.hash(), expected);
		}

		Box::pin(std::future::ready(None))
	}
}

impl AssertBestBlock {
	fn set_expected_best_block(&self, hash: Hash) {
		*self.0.lock() = Some(hash);
	}
}

const TEST_GOSSIP_DURATION: Duration = Duration::from_millis(500);

fn make_ids(keys: &[Ed25519Keyring]) -> AuthorityList {
	keys.iter().map(|&key| key.public().into()).map(|id| (id, 1)).collect()
}

fn create_keystore(authority: Ed25519Keyring) -> KeystorePtr {
	let keystore = MemoryKeystore::new();
	keystore
		.ed25519_generate_new(GRANDPA, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore.into()
}

async fn run_until_complete(future: impl Future + Unpin, net: &Arc<Mutex<GrandpaTestNet>>) {
	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	future::select(future, drive_to_completion).await;
}

// Spawns grandpa voters. Returns a future to spawn on the runtime.
fn initialize_grandpa(
	net: &mut GrandpaTestNet,
	peers: &[Ed25519Keyring],
) -> impl Future<Output = ()> {
	let voters = stream::FuturesUnordered::new();

	for (peer_id, key) in peers.iter().enumerate() {
		let keystore = create_keystore(*key);

		let (net_service, link) = {
			// temporary needed for some reason
			let link =
				net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(net.peers[peer_id].network_service().clone(), link)
		};
		let sync = net.peers[peer_id].sync_service().clone();

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore: Some(keystore),
				name: Some(format!("peer#{}", peer_id)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net_service,
			sync,
			voting_rule: (),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};
		let voter =
			run_grandpa_voter(grandpa_params).expect("all in order with client and network");

		fn assert_send<T: Send>(_: &T) {}
		assert_send(&voter);

		voters.push(voter);
	}

	voters.for_each(|_| async move {})
}

// run the voters to completion. provide a closure to be invoked after
// the voters are spawned but before blocking on them.
async fn run_to_completion_with<F>(
	blocks: u64,
	net: Arc<Mutex<GrandpaTestNet>>,
	peers: &[Ed25519Keyring],
	with: F,
) -> u64
where
	F: FnOnce(Handle) -> Option<Pin<Box<dyn Future<Output = ()>>>>,
{
	let mut wait_for = Vec::new();

	let highest_finalized = Arc::new(RwLock::new(0));

	if let Some(f) = (with)(Handle::current()) {
		wait_for.push(f);
	};

	for (peer_id, _) in peers.iter().enumerate() {
		let highest_finalized = highest_finalized.clone();
		let client = net.lock().peers[peer_id].client().clone();

		wait_for.push(Box::pin(
			client
				.finality_notification_stream()
				.take_while(move |n| {
					let mut highest_finalized = highest_finalized.write();
					if *n.header.number() > *highest_finalized {
						*highest_finalized = *n.header.number();
					}
					future::ready(n.header.number() < &blocks)
				})
				.collect::<Vec<_>>()
				.map(|_| ()),
		));
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(wait_for);

	run_until_complete(wait_for, &net).await;
	let highest_finalized = *highest_finalized.read();
	highest_finalized
}

async fn run_to_completion(
	blocks: u64,
	net: Arc<Mutex<GrandpaTestNet>>,
	peers: &[Ed25519Keyring],
) -> u64 {
	run_to_completion_with(blocks, net, peers, |_| None).await
}

fn add_scheduled_change(builder: &mut impl BlockBuilderExt, change: ScheduledChange<BlockNumber>) {
	builder
		.push_deposit_log_digest_item(DigestItem::Consensus(
			GRANDPA_ENGINE_ID,
			sp_consensus_grandpa::ConsensusLog::ScheduledChange(change).encode(),
		))
		.unwrap();
}

fn add_forced_change(
	builder: &mut impl BlockBuilderExt,
	median_last_finalized: BlockNumber,
	change: ScheduledChange<BlockNumber>,
) {
	builder
		.push_deposit_log_digest_item(DigestItem::Consensus(
			GRANDPA_ENGINE_ID,
			sp_consensus_grandpa::ConsensusLog::ForcedChange(median_last_finalized, change)
				.encode(),
		))
		.unwrap();
}

#[tokio::test]
async fn finalize_3_voters_no_observers() {
	sp_tracing::try_init_simple();
	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3, 0);
	tokio::spawn(initialize_grandpa(&mut net, peers));
	net.peer(0).push_blocks(20, false);
	net.run_until_sync().await;
	let hashof20 = net.peer(0).client().info().best_hash;

	for i in 0..3 {
		assert_eq!(net.peer(i).client().info().best_number, 20, "Peer #{} failed to sync", i);
		assert_eq!(net.peer(i).client().info().best_hash, hashof20, "Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(20, net.clone(), peers).await;

	// normally there's no justification for finalized blocks
	assert!(
		net.lock().peer(0).client().justifications(hashof20).unwrap().is_none(),
		"Extra justification for block#1",
	);
}

#[tokio::test]
async fn finalize_3_voters_1_full_observer() {
	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3, 1);
	tokio::spawn(initialize_grandpa(&mut net, peers));

	tokio::spawn({
		let peer_id = 3;
		let net_service = net.peers[peer_id].network_service().clone();
		let sync = net.peers[peer_id].sync_service().clone();
		let link = net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore: None,
				name: Some(format!("peer#{}", peer_id)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net_service,
			sync,
			voting_rule: (),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};

		run_grandpa_voter(grandpa_params).expect("all in order with client and network")
	});

	net.peer(0).push_blocks(20, false);

	let net = Arc::new(Mutex::new(net));
	let mut finality_notifications = Vec::new();

	for peer_id in 0..4 {
		let client = net.lock().peers[peer_id].client().clone();
		finality_notifications.push(
			client
				.finality_notification_stream()
				.take_while(|n| future::ready(n.header.number() < &20))
				.for_each(move |_| future::ready(())),
		);
	}

	// wait for all finalized on each.
	let wait_for = futures::future::join_all(finality_notifications).map(|_| ());

	run_until_complete(wait_for, &net).await;

	// all peers should have stored the justification for the best finalized block #20
	for peer_id in 0..4 {
		let client = net.lock().peers[peer_id].client().as_client();
		let justification =
			crate::aux_schema::best_justification::<_, Block>(&*client).unwrap().unwrap();

		assert_eq!(justification.justification.commit.target_number, 20);
	}
}

#[tokio::test]
async fn transition_3_voters_twice_1_full_observer() {
	sp_tracing::try_init_simple();
	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];

	let peers_b = &[Ed25519Keyring::Dave, Ed25519Keyring::Eve, Ed25519Keyring::Ferdie];

	let peers_c = &[Ed25519Keyring::Alice, Ed25519Keyring::Eve, Ed25519Keyring::Two];

	let observer = &[Ed25519Keyring::One];

	let all_peers = peers_a
		.iter()
		.chain(peers_b)
		.chain(peers_c)
		.chain(observer)
		.cloned()
		.collect::<HashSet<_>>(); // deduplicate

	let genesis_voters = make_ids(peers_a);

	let api = TestApi::new(genesis_voters);
	let net = Arc::new(Mutex::new(GrandpaTestNet::new(api, 8, 1)));

	let mut voters = Vec::new();
	for (peer_id, local_key) in all_peers.clone().into_iter().enumerate() {
		let keystore = create_keystore(local_key);

		let (net_service, link, sync) = {
			let net = net.lock();
			let link =
				net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(
				net.peers[peer_id].network_service().clone(),
				link,
				net.peers[peer_id].sync_service().clone(),
			)
		};

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore: Some(keystore),
				name: Some(format!("peer#{}", peer_id)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net_service,
			sync,
			voting_rule: (),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};

		voters
			.push(run_grandpa_voter(grandpa_params).expect("all in order with client and network"));
	}

	net.lock().peer(0).push_blocks(1, false);
	net.lock().run_until_sync().await;

	for (i, peer) in net.lock().peers().iter().enumerate() {
		let full_client = peer.client().as_client();
		assert_eq!(full_client.chain_info().best_number, 1, "Peer #{} failed to sync", i);

		let set: AuthoritySet<Hash, BlockNumber> =
			crate::aux_schema::load_authorities(&*full_client).unwrap();

		assert_eq!(set.current(), (0, make_ids(peers_a).as_slice()));
		assert_eq!(set.pending_changes().count(), 0);
	}

	{
		let net = net.clone();
		let client = net.lock().peers[0].client().clone();
		let peers_c = *peers_c;

		// wait for blocks to be finalized before generating new ones
		let block_production = client
			.finality_notification_stream()
			.take_while(|n| future::ready(n.header.number() < &30))
			.for_each(move |n| {
				match n.header.number() {
					1 => {
						// first 14 blocks.
						net.lock().peer(0).push_blocks(13, false);
					},
					14 => {
						// generate transition at block 15, applied at 20.
						net.lock().peer(0).generate_blocks(1, BlockOrigin::File, |mut builder| {
							add_scheduled_change(
								&mut builder,
								ScheduledChange { next_authorities: make_ids(peers_b), delay: 4 },
							);
							builder.build().unwrap().block
						});
						net.lock().peer(0).push_blocks(5, false);
					},
					20 => {
						// at block 21 we do another transition, but this time instant.
						// add more until we have 30.
						net.lock().peer(0).generate_blocks(1, BlockOrigin::File, |mut builder| {
							add_scheduled_change(
								&mut builder,
								ScheduledChange { next_authorities: make_ids(&peers_c), delay: 0 },
							);
							builder.build().unwrap().block
						});
						net.lock().peer(0).push_blocks(9, false);
					},
					_ => {},
				}

				future::ready(())
			});

		tokio::spawn(block_production);
	}

	let mut finality_notifications = Vec::new();

	for voter in voters {
		tokio::spawn(voter);
	}

	for (peer_id, _) in all_peers.into_iter().enumerate() {
		let client = net.lock().peers[peer_id].client().clone();
		finality_notifications.push(
			client
				.finality_notification_stream()
				.take_while(|n| future::ready(n.header.number() < &30))
				.for_each(move |_| future::ready(()))
				.map(move |()| {
					let full_client = client.as_client();
					let set: AuthoritySet<Hash, BlockNumber> =
						crate::aux_schema::load_authorities(&*full_client).unwrap();

					assert_eq!(set.current(), (2, make_ids(peers_c).as_slice()));
					assert_eq!(set.pending_changes().count(), 0);
				}),
		);
	}

	// wait for all finalized on each.
	let wait_for = ::futures::future::join_all(finality_notifications);

	run_until_complete(wait_for, &net).await;
}

#[tokio::test]
async fn justification_is_generated_periodically() {
	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3, 0);
	tokio::spawn(initialize_grandpa(&mut net, peers));
	net.peer(0).push_blocks(32, false);
	net.run_until_sync().await;

	let hashof32 = net.peer(0).client().info().best_hash;

	let net = Arc::new(Mutex::new(net));
	run_to_completion(32, net.clone(), peers).await;

	// when block#32 (justification_period) is finalized, justification
	// is required => generated
	for i in 0..3 {
		assert!(net.lock().peer(i).client().justifications(hashof32).unwrap().is_some());
	}
}

#[tokio::test]
async fn sync_justifications_on_change_blocks() {
	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let peers_b = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob];
	let voters = make_ids(peers_b);

	// 4 peers, 3 of them are authorities and participate in grandpa
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api, 3, 1);
	let voters = initialize_grandpa(&mut net, peers_a);

	// add 20 blocks
	net.peer(0).push_blocks(20, false);

	// at block 21 we do add a transition which is instant
	let hashof21 = net
		.peer(0)
		.generate_blocks(1, BlockOrigin::File, |mut builder| {
			add_scheduled_change(
				&mut builder,
				ScheduledChange { next_authorities: make_ids(peers_b), delay: 0 },
			);
			builder.build().unwrap().block
		})
		.pop()
		.unwrap();

	// add more blocks on top of it (until we have 25)
	net.peer(0).push_blocks(4, false);
	net.run_until_sync().await;

	for i in 0..4 {
		assert_eq!(net.peer(i).client().info().best_number, 25, "Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	tokio::spawn(voters);
	run_to_completion(25, net.clone(), peers_a).await;

	// the first 3 peers are grandpa voters and therefore have already finalized
	// block 21 and stored a justification
	for i in 0..3 {
		assert!(net.lock().peer(i).client().justifications(hashof21).unwrap().is_some());
	}

	// the last peer should get the justification by syncing from other peers
	futures::future::poll_fn(move |cx| {
		if net.lock().peer(3).client().justifications(hashof21).unwrap().is_none() {
			net.lock().poll(cx);
			Poll::Pending
		} else {
			Poll::Ready(())
		}
	})
	.await;
}

#[tokio::test]
async fn finalizes_multiple_pending_changes_in_order() {
	sp_tracing::try_init_simple();

	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let peers_b = &[Ed25519Keyring::Dave, Ed25519Keyring::Eve, Ed25519Keyring::Ferdie];
	let peers_c = &[Ed25519Keyring::Dave, Ed25519Keyring::Alice, Ed25519Keyring::Bob];

	let all_peers = &[
		Ed25519Keyring::Alice,
		Ed25519Keyring::Bob,
		Ed25519Keyring::Charlie,
		Ed25519Keyring::Dave,
		Ed25519Keyring::Eve,
		Ed25519Keyring::Ferdie,
	];
	let genesis_voters = make_ids(peers_a);

	// 6 peers, 3 of them are authorities and participate in grandpa from genesis
	// but all of them will be part of the voter set eventually so they should be
	// all added to the network as authorities
	let api = TestApi::new(genesis_voters);
	let mut net = GrandpaTestNet::new(api, 6, 0);
	tokio::spawn(initialize_grandpa(&mut net, all_peers));

	// add 20 blocks
	net.peer(0).push_blocks(20, false);

	// at block 21 we do add a transition which is instant
	net.peer(0).generate_blocks(1, BlockOrigin::File, |mut builder| {
		add_scheduled_change(
			&mut builder,
			ScheduledChange { next_authorities: make_ids(peers_b), delay: 0 },
		);
		builder.build().unwrap().block
	});

	// add more blocks on top of it (until we have 25)
	net.peer(0).push_blocks(4, false);

	// at block 26 we add another which is enacted at block 30
	net.peer(0).generate_blocks(1, BlockOrigin::File, |mut builder| {
		add_scheduled_change(
			&mut builder,
			ScheduledChange { next_authorities: make_ids(peers_c), delay: 4 },
		);
		builder.build().unwrap().block
	});

	// add more blocks on top of it (until we have 30)
	net.peer(0).push_blocks(4, false);

	net.run_until_sync().await;

	// all peers imported both change blocks
	for i in 0..6 {
		assert_eq!(net.peer(i).client().info().best_number, 30, "Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));
	run_to_completion(30, net.clone(), all_peers).await;
}

#[tokio::test]
async fn force_change_to_new_set() {
	sp_tracing::try_init_simple();
	// two of these guys are offline.
	let genesis_authorities = &[
		Ed25519Keyring::Alice,
		Ed25519Keyring::Bob,
		Ed25519Keyring::Charlie,
		Ed25519Keyring::One,
		Ed25519Keyring::Two,
	];
	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let api = TestApi::new(make_ids(genesis_authorities));

	let voters = make_ids(peers_a);
	let mut net = GrandpaTestNet::new(api, 3, 0);
	let voters_future = initialize_grandpa(&mut net, peers_a);
	let net = Arc::new(Mutex::new(net));

	net.lock().peer(0).generate_blocks(1, BlockOrigin::File, |mut builder| {
		// add a forced transition at block 12.
		add_forced_change(
			&mut builder,
			0,
			ScheduledChange { next_authorities: voters.clone(), delay: 10 },
		);

		// add a normal transition too to ensure that forced changes take priority.
		add_scheduled_change(
			&mut builder,
			ScheduledChange { next_authorities: make_ids(genesis_authorities), delay: 5 },
		);

		builder.build().unwrap().block
	});

	net.lock().peer(0).push_blocks(25, false);
	net.lock().run_until_sync().await;

	for (i, peer) in net.lock().peers().iter().enumerate() {
		assert_eq!(peer.client().info().best_number, 26, "Peer #{} failed to sync", i);

		let full_client = peer.client().as_client();
		let set: AuthoritySet<Hash, BlockNumber> =
			crate::aux_schema::load_authorities(&*full_client).unwrap();

		assert_eq!(set.current(), (1, voters.as_slice()));
		assert_eq!(set.pending_changes().count(), 0);
	}

	// it will only finalize if the forced transition happens.
	// we add_blocks after the voters are spawned because otherwise
	// the link-halves have the wrong AuthoritySet
	tokio::spawn(voters_future);
	run_to_completion(25, net, peers_a).await;
}

#[tokio::test]
async fn allows_reimporting_change_blocks() {
	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let peers_b = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api.clone(), 3, 0);

	let client = net.peer(0).client().clone();
	let (mut block_import, ..) = net.make_block_import(client.clone());

	let full_client = client.as_client();
	let mut builder = full_client
		.new_block_at(full_client.chain_info().genesis_hash, Default::default(), false)
		.unwrap();

	add_scheduled_change(
		&mut builder,
		ScheduledChange { next_authorities: make_ids(peers_b), delay: 0 },
	);
	let block = builder.build().unwrap().block;

	let block = || {
		let block = block.clone();
		let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
		import.body = Some(block.extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		import
	};

	assert_eq!(
		block_import.import_block(block()).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			needs_justification: true,
			clear_justification_requests: false,
			bad_justification: false,
			is_new_best: true,
			header_only: false,
		}),
	);

	assert_eq!(block_import.import_block(block()).await.unwrap(), ImportResult::AlreadyInChain);
}

#[tokio::test]
async fn test_bad_justification() {
	let peers_a = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let peers_b = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob];
	let voters = make_ids(peers_a);
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api.clone(), 3, 0);

	let client = net.peer(0).client().clone();
	let (mut block_import, ..) = net.make_block_import(client.clone());

	let full_client = client.as_client();
	let mut builder = full_client
		.new_block_at(full_client.chain_info().genesis_hash, Default::default(), false)
		.unwrap();

	add_scheduled_change(
		&mut builder,
		ScheduledChange { next_authorities: make_ids(peers_b), delay: 0 },
	);

	let block = builder.build().unwrap().block;

	let block = || {
		let block = block.clone();
		let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
		import.justifications = Some(Justifications::from((GRANDPA_ENGINE_ID, Vec::new())));
		import.body = Some(block.extrinsics);
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

		import
	};

	assert_eq!(
		block_import.import_block(block()).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			needs_justification: true,
			clear_justification_requests: false,
			bad_justification: true,
			is_new_best: true,
			..Default::default()
		}),
	);

	assert_eq!(block_import.import_block(block()).await.unwrap(), ImportResult::AlreadyInChain);
}

#[tokio::test]
async fn voter_persists_its_votes() {
	use futures::future;
	use std::sync::atomic::{AtomicUsize, Ordering};

	sp_tracing::try_init_simple();

	// we have two authorities but we'll only be running the voter for alice
	// we are going to be listening for the prevotes it casts
	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob];
	let voters = make_ids(peers);

	// alice has a chain with 20 blocks
	let mut net = GrandpaTestNet::new(TestApi::new(voters.clone()), 2, 0);

	// create the communication layer for bob, but don't start any
	// voter. instead we'll listen for the prevote that alice casts
	// and cast our own manually
	let bob_keystore = create_keystore(peers[1]);
	let bob_network = {
		let config = Config {
			gossip_duration: TEST_GOSSIP_DURATION,
			justification_period: 32,
			keystore: Some(bob_keystore.clone()),
			name: Some(format!("peer#{}", 1)),
			local_role: Role::Authority,
			observer_enabled: true,
			telemetry: None,
			protocol_name: grandpa_protocol_name::NAME.into(),
		};

		let set_state = {
			let bob_client = net.peer(1).client().clone();
			let (_, _, link) = net.make_block_import(bob_client);
			let LinkHalf { persistent_data, .. } = link.lock().take().unwrap();
			let PersistentData { set_state, .. } = persistent_data;
			set_state
		};

		communication::NetworkBridge::new(
			net.peers[1].network_service().clone(),
			net.peers[1].sync_service().clone(),
			config.clone(),
			set_state,
			None,
			None,
		)
	};

	// spawn two voters for alice.
	// half-way through the test, we stop one and start the other.
	let (alice_voter1, abort) = future::abortable({
		let keystore = create_keystore(peers[0]);

		let (net_service, link) = {
			// temporary needed for some reason
			let link = net.peers[0].data.lock().take().expect("link initialized at startup; qed");
			(net.peers[0].network_service().clone(), link)
		};
		let sync = net.peers[0].sync_service().clone();

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore: Some(keystore),
				name: Some(format!("peer#{}", 0)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net_service,
			sync,
			voting_rule: VotingRulesBuilder::default().build(),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};

		run_grandpa_voter(grandpa_params).expect("all in order with client and network")
	});

	fn alice_voter2(
		peers: &[Ed25519Keyring],
		net: Arc<Mutex<GrandpaTestNet>>,
	) -> impl Future<Output = ()> + Send {
		let keystore = create_keystore(peers[0]);
		let mut net = net.lock();

		// we add a new peer to the test network and we'll use
		// the network service of this new peer
		net.add_authority_peer();
		let net_service = net.peers[2].network_service().clone();
		let sync = net.peers[2].sync_service().clone();
		// but we'll reuse the client from the first peer (alice_voter1)
		// since we want to share the same database, so that we can
		// read the persisted state after aborting alice_voter1.
		let alice_client = net.peer(0).client().clone();

		let (_block_import, _, link) = net.make_block_import(alice_client);
		let link = link.lock().take().unwrap();

		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore: Some(keystore),
				name: Some(format!("peer#{}", 0)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net_service,
			sync,
			voting_rule: VotingRulesBuilder::default().build(),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};

		run_grandpa_voter(grandpa_params)
			.expect("all in order with client and network")
			.map(move |r| {
				// we need to keep the block_import alive since it owns the
				// sender for the voter commands channel, if that gets dropped
				// then the voter will stop
				drop(_block_import);
				r
			})
	}

	tokio::spawn(alice_voter1);

	net.peer(0).push_blocks(20, false);
	net.run_until_sync().await;

	assert_eq!(net.peer(0).client().info().best_number, 20, "Peer #{} failed to sync", 0);

	let net = Arc::new(Mutex::new(net));

	let (exit_tx, exit_rx) = futures::channel::oneshot::channel::<()>();

	{
		let (round_rx, round_tx) = bob_network.round_communication(
			Some((peers[1].public().into(), bob_keystore).into()),
			communication::Round(1),
			communication::SetId(0),
			Arc::new(VoterSet::new(voters).unwrap()),
			HasVoted::No,
		);

		tokio::spawn(bob_network);

		let round_tx = Arc::new(Mutex::new(round_tx));
		let exit_tx = Arc::new(Mutex::new(Some(exit_tx)));

		let net = net.clone();
		let state = Arc::new(AtomicUsize::new(0));

		tokio::spawn(round_rx.for_each(move |signed| {
			let net2 = net.clone();
			let net = net.clone();
			let abort = abort.clone();
			let round_tx = round_tx.clone();
			let state = state.clone();
			let exit_tx = exit_tx.clone();

			async move {
				if state.compare_exchange(0, 1, Ordering::SeqCst, Ordering::SeqCst).unwrap() == 0 {
					// the first message we receive should be a prevote from alice.
					let prevote = match signed.message {
						finality_grandpa::Message::Prevote(prevote) => prevote,
						_ => panic!("voter should prevote."),
					};

					// its chain has 20 blocks and the voter targets 3/4 of the
					// unfinalized chain, so the vote should be for block 15
					assert_eq!(prevote.target_number, 15);

					// we push 20 more blocks to alice's chain
					net.lock().peer(0).push_blocks(20, false);

					let interval =
						futures::stream::unfold(Delay::new(Duration::from_millis(200)), |delay| {
							Box::pin(async move {
								delay.await;
								Some(((), Delay::new(Duration::from_millis(200))))
							})
						});

					interval
						.take_while(move |_| {
							future::ready(net2.lock().peer(1).client().info().best_number != 40)
						})
						.for_each(|_| future::ready(()))
						.await;

					let block_30_hash =
						net.lock().peer(0).client().as_client().hash(30).unwrap().unwrap();

					// we restart alice's voter
					abort.abort();
					tokio::spawn(alice_voter2(peers, net.clone()));

					// and we push our own prevote for block 30
					let prevote =
						finality_grandpa::Prevote { target_number: 30, target_hash: block_30_hash };

					// One should either be calling `Sink::send` or `Sink::start_send` followed
					// by `Sink::poll_complete` to make sure items are being flushed. Given that
					// we send in a loop including a delay until items are received, this can be
					// ignored for the sake of reduced complexity.
					Pin::new(&mut *round_tx.lock())
						.start_send(finality_grandpa::Message::Prevote(prevote))
						.unwrap();
				} else if state.compare_exchange(1, 2, Ordering::SeqCst, Ordering::SeqCst).unwrap() ==
					1
				{
					// the next message we receive should be our own prevote
					let prevote = match signed.message {
						finality_grandpa::Message::Prevote(prevote) => prevote,
						_ => panic!("We should receive our own prevote."),
					};

					// targeting block 30
					assert!(prevote.target_number == 30);

				// after alice restarts it should send its previous prevote
				// therefore we won't ever receive it again since it will be a
				// known message on the gossip layer
				} else if state.compare_exchange(2, 3, Ordering::SeqCst, Ordering::SeqCst).unwrap() ==
					2
				{
					// we then receive a precommit from alice for block 15
					// even though we casted a prevote for block 30
					let precommit = match signed.message {
						finality_grandpa::Message::Precommit(precommit) => precommit,
						_ => panic!("voter should precommit."),
					};

					assert!(precommit.target_number == 15);

					// signal exit
					exit_tx.clone().lock().take().unwrap().send(()).unwrap();
				} else {
					panic!()
				}
			}
		}));
	}

	run_until_complete(exit_rx.into_future(), &net).await;
}

#[tokio::test]
async fn finalize_3_voters_1_light_observer() {
	sp_tracing::try_init_simple();
	let authorities = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];
	let voters = make_ids(authorities);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 3, 1);
	let voters = initialize_grandpa(&mut net, authorities);
	let observer = observer::run_grandpa_observer(
		Config {
			gossip_duration: TEST_GOSSIP_DURATION,
			justification_period: 32,
			keystore: None,
			name: Some("observer".to_string()),
			local_role: Role::Full,
			observer_enabled: true,
			telemetry: None,
			protocol_name: grandpa_protocol_name::NAME.into(),
		},
		net.peers[3].data.lock().take().expect("link initialized at startup; qed"),
		net.peers[3].network_service().clone(),
		net.peers[3].sync_service().clone(),
	)
	.unwrap();
	net.peer(0).push_blocks(20, false);
	net.run_until_sync().await;

	for i in 0..4 {
		assert_eq!(net.peer(i).client().info().best_number, 20, "Peer #{} failed to sync", i);
	}

	let net = Arc::new(Mutex::new(net));

	tokio::spawn(voters);
	tokio::spawn(observer);
	run_to_completion(20, net.clone(), authorities).await;
}

#[tokio::test]
async fn voter_catches_up_to_latest_round_when_behind() {
	sp_tracing::try_init_simple();

	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob];
	let voters = make_ids(peers);

	let net = GrandpaTestNet::new(TestApi::new(voters), 2, 0);

	let net = Arc::new(Mutex::new(net));
	let mut finality_notifications = Vec::new();

	let voter = |keystore,
	             peer_id,
	             link,
	             net: Arc<Mutex<GrandpaTestNet>>|
	 -> Pin<Box<dyn Future<Output = ()> + Send>> {
		let mut net = net.lock();
		let grandpa_params = GrandpaParams {
			config: Config {
				gossip_duration: TEST_GOSSIP_DURATION,
				justification_period: 32,
				keystore,
				name: Some(format!("peer#{}", peer_id)),
				local_role: Role::Authority,
				observer_enabled: true,
				telemetry: None,
				protocol_name: grandpa_protocol_name::NAME.into(),
			},
			link,
			network: net.peer(peer_id).network_service().clone(),
			sync: net.peer(peer_id).sync_service().clone(),
			voting_rule: (),
			prometheus_registry: None,
			shared_voter_state: SharedVoterState::empty(),
			telemetry: None,
		};

		Box::pin(run_grandpa_voter(grandpa_params).expect("all in order with client and network"))
	};

	// spawn authorities
	for (peer_id, key) in peers.iter().enumerate() {
		let (client, link) = {
			let net = net.lock();
			let link =
				net.peers[peer_id].data.lock().take().expect("link initialized at startup; qed");
			(net.peers[peer_id].client().clone(), link)
		};

		finality_notifications.push(
			client
				.finality_notification_stream()
				.take_while(|n| future::ready(n.header.number() < &50))
				.for_each(move |_| future::ready(())),
		);

		let keystore = create_keystore(*key);

		let voter = voter(Some(keystore), peer_id, link, net.clone());

		tokio::spawn(voter);
	}

	net.lock().peer(0).push_blocks(50, false);
	net.lock().run_until_sync().await;

	// wait for them to finalize block 50. since they'll vote on 3/4 of the
	// unfinalized chain it will take at least 4 rounds to do it.
	let wait_for_finality = ::futures::future::join_all(finality_notifications);

	// spawn a new voter, it should be behind by at least 4 rounds and should be
	// able to catch up to the latest round
	let test = {
		let net = net.clone();

		wait_for_finality.then(move |_| {
			net.lock().add_authority_peer();

			let link = {
				let net = net.lock();
				let mut link = net.peers[2].data.lock();
				link.take().expect("link initialized at startup; qed")
			};
			let set_state = link.persistent_data.set_state.clone();
			tokio::spawn(voter(None, 2, link, net.clone()));

			let start_time = std::time::Instant::now();
			let timeout = Duration::from_secs(5 * 60);
			let wait_for_catch_up = futures::future::poll_fn(move |_| {
				// The voter will start at round 1 and since everyone else is
				// already at a later round the only way to get to round 4 (or
				// later) is by issuing a catch up request.
				if set_state.read().last_completed_round().number >= 4 {
					Poll::Ready(())
				} else if start_time.elapsed() > timeout {
					panic!("Timed out while waiting for catch up to happen")
				} else {
					Poll::Pending
				}
			});

			wait_for_catch_up
		})
	};

	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	future::select(test, drive_to_completion).await;
}

type TestEnvironment<N, S, SC, VR> =
	Environment<substrate_test_runtime_client::Backend, Block, TestClient, N, S, SC, VR>;

fn test_environment_with_select_chain<N, S, VR, SC>(
	link: &TestLinkHalf,
	keystore: Option<KeystorePtr>,
	network_service: N,
	sync_service: S,
	select_chain: SC,
	voting_rule: VR,
) -> TestEnvironment<N, S, SC, VR>
where
	N: NetworkT<Block>,
	S: SyncingT<Block>,
	VR: VotingRule<Block, TestClient>,
{
	let PersistentData { ref authority_set, ref set_state, .. } = link.persistent_data;

	let config = Config {
		gossip_duration: TEST_GOSSIP_DURATION,
		justification_period: 32,
		keystore,
		name: None,
		local_role: Role::Authority,
		observer_enabled: true,
		telemetry: None,
		protocol_name: grandpa_protocol_name::NAME.into(),
	};

	let network = NetworkBridge::new(
		network_service.clone(),
		sync_service,
		config.clone(),
		set_state.clone(),
		None,
		None,
	);

	Environment {
		authority_set: authority_set.clone(),
		config: config.clone(),
		client: link.client.clone(),
		select_chain,
		set_id: authority_set.set_id(),
		voter_set_state: set_state.clone(),
		voters: Arc::new(authority_set.current_authorities()),
		network,
		voting_rule,
		metrics: None,
		justification_sender: None,
		telemetry: None,
		_phantom: PhantomData,
	}
}

fn test_environment<N, S, VR>(
	link: &TestLinkHalf,
	keystore: Option<KeystorePtr>,
	network_service: N,
	sync_service: S,
	voting_rule: VR,
) -> TestEnvironment<N, S, LongestChain<substrate_test_runtime_client::Backend, Block>, VR>
where
	N: NetworkT<Block>,
	S: SyncingT<Block>,
	VR: VotingRule<Block, TestClient>,
{
	test_environment_with_select_chain(
		link,
		keystore,
		network_service,
		sync_service,
		link.select_chain.clone(),
		voting_rule,
	)
}

#[tokio::test]
async fn grandpa_environment_respects_voting_rules() {
	use finality_grandpa::voter::Environment;

	let peers = &[Ed25519Keyring::Alice];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 1, 0);
	let peer = net.peer(0);
	let network_service = peer.network_service().clone();
	let sync_service = peer.sync_service().clone();
	let link = peer.data.lock().take().unwrap();

	// add 21 blocks
	let hashes = peer.push_blocks(21, false);

	// create an environment with no voting rule restrictions
	let unrestricted_env =
		test_environment(&link, None, network_service.clone(), sync_service.clone(), ());

	// another with 3/4 unfinalized chain voting rule restriction
	let three_quarters_env = test_environment(
		&link,
		None,
		network_service.clone(),
		sync_service.clone(),
		voting_rule::ThreeQuartersOfTheUnfinalizedChain,
	);

	// and another restricted with the default voting rules: i.e. 3/4 rule and
	// always below best block
	let default_env = test_environment(
		&link,
		None,
		network_service.clone(),
		sync_service,
		VotingRulesBuilder::default().build(),
	);

	// the unrestricted environment should just return the best block
	assert_eq!(
		unrestricted_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		21,
	);

	// both the other environments should return block 16, which is 3/4 of the
	// way in the unfinalized chain
	assert_eq!(
		three_quarters_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		16,
	);

	assert_eq!(
		default_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		16,
	);

	// we finalize block 19 with block 21 being the best block
	peer.client().finalize_block(hashes[18], None, false).unwrap();

	// the 3/4 environment should propose block 21 for voting
	assert_eq!(
		three_quarters_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		21,
	);

	// while the default environment will always still make sure we don't vote
	// on the best block (2 behind)
	assert_eq!(
		default_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		19,
	);

	// we finalize block 21 with block 21 being the best block
	let hashof21 = hashes[20];
	peer.client().finalize_block(hashof21, None, false).unwrap();

	// even though the default environment will always try to not vote on the
	// best block, there's a hard rule that we can't cast any votes lower than
	// the given base (#21).
	assert_eq!(
		default_env
			.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		21,
	);
}

#[tokio::test]
async fn grandpa_environment_passes_actual_best_block_to_voting_rules() {
	// NOTE: this is a "regression" test since initially we were not passing the
	// best block to the voting rules
	use finality_grandpa::voter::Environment;

	let peers = &[Ed25519Keyring::Alice];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 1, 0);
	let peer = net.peer(0);
	let network_service = peer.network_service().clone();
	let sync_service = peer.sync_service().clone();
	let link = peer.data.lock().take().unwrap();
	let client = peer.client().as_client().clone();
	let select_chain = MockSelectChain::default();

	// add 42 blocks
	peer.push_blocks(42, false);

	// create an environment with a voting rule that always restricts votes to
	// before the best block by 5 blocks
	let env = test_environment_with_select_chain(
		&link,
		None,
		network_service.clone(),
		sync_service,
		select_chain.clone(),
		voting_rule::BeforeBestBlockBy(5),
	);

	// both best block and finality target are pointing to the same latest block,
	// therefore we must restrict our vote on top of the given target (#21)
	let hashof21 = client.expect_block_hash_from_id(&BlockId::Number(21)).unwrap();
	select_chain.set_best_chain(client.expect_header(hashof21).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof21).unwrap().hash());

	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		16,
	);

	// the returned finality target is already 11 blocks from the best block,
	// therefore there should be no further restriction by the voting rule
	let hashof10 = client.expect_block_hash_from_id(&BlockId::Number(10)).unwrap();
	select_chain.set_best_chain(client.expect_header(hashof21).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof10).unwrap().hash());

	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.1,
		10,
	);
}

#[tokio::test]
async fn grandpa_environment_checks_if_best_block_is_descendent_of_finality_target() {
	sp_tracing::try_init_simple();
	use finality_grandpa::voter::Environment;

	let peers = &[Ed25519Keyring::Alice];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 1, 0);
	let peer = net.peer(0);
	let network_service = peer.network_service().clone();
	let sync_service = peer.sync_service().clone();
	let link = peer.data.lock().take().unwrap();
	let client = peer.client().as_client().clone();
	let select_chain = MockSelectChain::default();
	let voting_rule = AssertBestBlock::default();
	let env = test_environment_with_select_chain(
		&link,
		None,
		network_service.clone(),
		sync_service.clone(),
		select_chain.clone(),
		voting_rule.clone(),
	);

	// create a chain that is 10 blocks long
	peer.push_blocks(10, false);

	let hashof5_a = client.expect_block_hash_from_id(&BlockId::Number(5)).unwrap();
	let hashof10_a = client.expect_block_hash_from_id(&BlockId::Number(10)).unwrap();

	// create a fork starting at block 4 that is 6 blocks long
	let fork = peer.generate_blocks_at(
		BlockId::Number(4),
		6,
		BlockOrigin::File,
		|mut builder| {
			builder.push_deposit_log_digest_item(DigestItem::Other(vec![1])).unwrap();
			builder.build().unwrap().block
		},
		false,
		false,
		true,
		ForkChoiceStrategy::LongestChain,
	);

	let hashof5_b = *fork.first().unwrap();
	let hashof10_b = *fork.last().unwrap();

	// returning a finality target that's higher than the best block is inconsistent,
	// therefore the best block should be set to be the same block as the target
	select_chain.set_best_chain(client.expect_header(hashof5_a).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof10_a).unwrap().hash());
	voting_rule.set_expected_best_block(hashof10_a);

	// the voting rule will internally assert that the best block that was passed was `hashof10_a`,
	// instead of the one returned by `SelectChain`
	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.0,
		hashof10_a,
	);

	// best block and finality target are blocks at the same height but on different forks,
	// we should override the initial best block (#5B) with the target block (#5A)
	select_chain.set_best_chain(client.expect_header(hashof5_b).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof5_a).unwrap().hash());
	voting_rule.set_expected_best_block(hashof5_a);

	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.0,
		hashof5_a,
	);

	// best block is higher than finality target but it's on a different fork,
	// we should override the initial best block (#5A) with the target block (#5B)
	select_chain.set_best_chain(client.expect_header(hashof10_b).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof5_a).unwrap().hash());
	voting_rule.set_expected_best_block(hashof5_a);

	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.0,
		hashof5_a,
	);

	// best block is higher than finality target and it's on the same fork,
	// the best block passed to the voting rule should not be overriden
	select_chain.set_best_chain(client.expect_header(hashof10_a).unwrap());
	select_chain.set_finality_target(client.expect_header(hashof5_a).unwrap().hash());
	voting_rule.set_expected_best_block(hashof10_a);

	assert_eq!(
		env.best_chain_containing(peer.client().info().finalized_hash)
			.await
			.unwrap()
			.unwrap()
			.0,
		hashof5_a,
	);
}

#[tokio::test]
async fn grandpa_environment_never_overwrites_round_voter_state() {
	use finality_grandpa::voter::Environment;

	let peers = &[Ed25519Keyring::Alice];
	let voters = make_ids(peers);

	let mut net = GrandpaTestNet::new(TestApi::new(voters), 1, 0);
	let peer = net.peer(0);
	let network_service = peer.network_service().clone();
	let sync_service = peer.sync_service().clone();
	let link = peer.data.lock().take().unwrap();

	let keystore = create_keystore(peers[0]);
	let environment =
		test_environment(&link, Some(keystore), network_service.clone(), sync_service, ());

	let round_state = || finality_grandpa::round::State::genesis(Default::default());
	let base = || Default::default();
	let historical_votes = || finality_grandpa::HistoricalVotes::new();

	let get_current_round = |n| {
		let current_rounds = environment
			.voter_set_state
			.read()
			.with_current_round(n)
			.map(|(_, current_rounds)| current_rounds.clone())
			.ok()?;

		Some(current_rounds.get(&n).unwrap().clone())
	};

	// round 2 should not be tracked
	assert_eq!(get_current_round(2), None);

	// after completing round 1 we should start tracking round 2
	environment.completed(1, round_state(), base(), &historical_votes()).unwrap();

	assert_eq!(get_current_round(2).unwrap(), HasVoted::No);

	// we need to call `round_data` for the next round to pick up
	// from the keystore which authority id we'll be using to vote
	environment.round_data(2);

	let info = peer.client().info();

	let prevote =
		finality_grandpa::Prevote { target_hash: info.best_hash, target_number: info.best_number };

	// we prevote for round 2 which should lead to us updating the voter state
	environment.prevoted(2, prevote.clone()).unwrap();

	let has_voted = get_current_round(2).unwrap();

	assert_matches!(has_voted, HasVoted::Yes(_, _));
	assert_eq!(*has_voted.prevote().unwrap(), prevote);

	// if we report round 1 as completed again we should not overwrite the
	// voter state for round 2
	environment.completed(1, round_state(), base(), &historical_votes()).unwrap();

	assert_matches!(get_current_round(2).unwrap(), HasVoted::Yes(_, _));
}

#[tokio::test]
async fn justification_with_equivocation() {
	use sp_application_crypto::Pair;

	// we have 100 authorities
	let pairs = (0..100).map(|n| AuthorityPair::from_seed(&[n; 32])).collect::<Vec<_>>();
	let voters = pairs.iter().map(AuthorityPair::public).map(|id| (id, 1)).collect::<Vec<_>>();
	let api = TestApi::new(voters.clone());
	let mut net = GrandpaTestNet::new(api.clone(), 1, 0);

	// we create a basic chain with 3 blocks (no forks)
	net.peer(0).push_blocks(3, false);

	let client = net.peer(0).client().as_client().clone();
	let hashof1 = client.expect_block_hash_from_id(&BlockId::Number(1)).unwrap();
	let hashof2 = client.expect_block_hash_from_id(&BlockId::Number(2)).unwrap();
	let hashof3 = client.expect_block_hash_from_id(&BlockId::Number(3)).unwrap();
	let block1 = client.expect_header(hashof1).unwrap();
	let block2 = client.expect_header(hashof2).unwrap();
	let block3 = client.expect_header(hashof3).unwrap();

	let set_id = 0;
	let justification = {
		let round = 1;

		let make_precommit = |target_hash, target_number, pair: &AuthorityPair| {
			let precommit = finality_grandpa::Precommit { target_hash, target_number };

			let msg = finality_grandpa::Message::Precommit(precommit.clone());
			let encoded = sp_consensus_grandpa::localized_payload(round, set_id, &msg);

			let precommit = finality_grandpa::SignedPrecommit {
				precommit: precommit.clone(),
				signature: pair.sign(&encoded[..]),
				id: pair.public(),
			};

			precommit
		};

		let mut precommits = Vec::new();

		// we have 66/100 votes for block #3 and therefore do not have threshold to finalize
		for pair in pairs.iter().take(66) {
			let precommit = make_precommit(block3.hash(), *block3.number(), pair);
			precommits.push(precommit);
		}

		// we create an equivocation for the 67th validator targetting blocks #1 and #2.
		// this should be accounted as "voting for all blocks" and therefore block #3 will
		// have 67/100 votes, reaching finality threshold.
		{
			precommits.push(make_precommit(block1.hash(), *block1.number(), &pairs[66]));
			precommits.push(make_precommit(block2.hash(), *block2.number(), &pairs[66]));
		}

		let commit = finality_grandpa::Commit {
			target_hash: block3.hash(),
			target_number: *block3.number(),
			precommits,
		};

		GrandpaJustification::from_commit(&client, round, commit).unwrap()
	};

	// the justification should include the minimal necessary vote ancestry and
	// the commit should be valid
	assert!(justification.verify(set_id, &voters).is_ok());
}

#[tokio::test]
async fn imports_justification_for_regular_blocks_on_import() {
	// NOTE: this is a regression test since initially we would only import
	// justifications for authority change blocks, and would discard any
	// existing justification otherwise.
	let peers = &[Ed25519Keyring::Alice];
	let voters = make_ids(peers);
	let api = TestApi::new(voters);
	let mut net = GrandpaTestNet::new(api.clone(), 1, 0);

	let client = net.peer(0).client().clone();
	let (mut block_import, ..) = net.make_block_import(client.clone());

	let full_client = client.as_client();
	let builder = full_client
		.new_block_at(full_client.chain_info().genesis_hash, Default::default(), false)
		.unwrap();
	let block = builder.build().unwrap().block;

	let block_hash = block.hash();

	// create a valid justification, with one precommit targeting the block
	let justification = {
		let round = 1;
		let set_id = 0;

		let precommit = finality_grandpa::Precommit {
			target_hash: block_hash,
			target_number: *block.header.number(),
		};

		let msg = finality_grandpa::Message::Precommit(precommit.clone());
		let encoded = sp_consensus_grandpa::localized_payload(round, set_id, &msg);
		let signature = peers[0].sign(&encoded[..]).into();

		let precommit = finality_grandpa::SignedPrecommit {
			precommit,
			signature,
			id: peers[0].public().into(),
		};

		let commit = finality_grandpa::Commit {
			target_hash: block_hash,
			target_number: *block.header.number(),
			precommits: vec![precommit],
		};

		GrandpaJustification::from_commit(&full_client, round, commit).unwrap()
	};

	// we import the block with justification attached
	let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
	import.justifications = Some((GRANDPA_ENGINE_ID, justification.encode()).into());
	import.body = Some(block.extrinsics);
	import.fork_choice = Some(ForkChoiceStrategy::LongestChain);

	assert_eq!(
		block_import.import_block(import).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			needs_justification: false,
			clear_justification_requests: false,
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);

	// the justification should be imported and available from the client
	assert!(client.justifications(block_hash).unwrap().is_some());
}

#[tokio::test]
async fn grandpa_environment_doesnt_send_equivocation_reports_for_itself() {
	use finality_grandpa::voter::Environment;

	let alice = Ed25519Keyring::Alice;
	let voters = make_ids(&[alice]);

	let environment = {
		let mut net = GrandpaTestNet::new(TestApi::new(voters), 1, 0);
		let peer = net.peer(0);
		let network_service = peer.network_service().clone();
		let sync_service = peer.sync_service().clone();
		let link = peer.data.lock().take().unwrap();
		let keystore = create_keystore(alice);
		test_environment(&link, Some(keystore), network_service.clone(), sync_service, ())
	};

	let signed_prevote = {
		let prevote = finality_grandpa::Prevote { target_hash: H256::random(), target_number: 1 };

		let signed = alice.sign(&[]).into();
		(prevote, signed)
	};

	let mut equivocation = finality_grandpa::Equivocation {
		round_number: 1,
		identity: alice.public().into(),
		first: signed_prevote.clone(),
		second: signed_prevote.clone(),
	};

	// we need to call `round_data` to pick up from the keystore which
	// authority id we'll be using to vote
	environment.round_data(1);

	// reporting the equivocation should fail since the offender is a local
	// authority (i.e. we have keys in our keystore for the given id)
	let equivocation_proof = sp_consensus_grandpa::Equivocation::Prevote(equivocation.clone());
	assert!(matches!(environment.report_equivocation(equivocation_proof), Err(Error::Safety(_))));

	// if we set the equivocation offender to another id for which we don't have
	// keys it should work
	equivocation.identity = TryFrom::try_from(&[1; 32][..]).unwrap();
	let equivocation_proof = sp_consensus_grandpa::Equivocation::Prevote(equivocation);
	assert!(environment.report_equivocation(equivocation_proof).is_ok());
}

#[tokio::test]
async fn revert_prunes_authority_changes() {
	sp_tracing::try_init_simple();

	let peers = &[Ed25519Keyring::Alice, Ed25519Keyring::Bob, Ed25519Keyring::Charlie];

	type TestBlockBuilder<'a> =
		BlockBuilder<'a, Block, PeersFullClient, substrate_test_runtime_client::Backend>;
	let edit_block = |mut builder: TestBlockBuilder| {
		add_scheduled_change(
			&mut builder,
			ScheduledChange { next_authorities: make_ids(peers), delay: 0 },
		);
		builder.build().unwrap().block
	};

	let api = TestApi::new(make_ids(peers));

	let mut net = GrandpaTestNet::new(api, 3, 0);
	tokio::spawn(initialize_grandpa(&mut net, peers));

	let peer = net.peer(0);
	let client = peer.client().as_client();

	// Test scenario: (X) = auth-change, 24 = revert-point
	//
	//              +---------(27)
	//             /
	// 0---(21)---23---24---25---(28)---30
	//                  ^    \
	//        revert-point    +------(29)

	// Construct canonical chain

	// add 20 blocks
	peer.push_blocks(20, false);
	// at block 21 we add an authority transition
	peer.generate_blocks(1, BlockOrigin::File, edit_block);
	// add more blocks on top of it (until we have 24)
	peer.push_blocks(3, false);
	// add more blocks on top of it (until we have 27)
	peer.push_blocks(3, false);
	// at block 28 we add an authority transition
	peer.generate_blocks(1, BlockOrigin::File, edit_block);
	// add more blocks on top of it (until we have 30)
	peer.push_blocks(2, false);

	// Fork before revert point

	// add more blocks on top of block 23 (until we have 26)
	let hash = peer
		.generate_blocks_at(
			BlockId::Number(23),
			3,
			BlockOrigin::File,
			|mut builder| {
				builder.push_deposit_log_digest_item(DigestItem::Other(vec![1])).unwrap();
				builder.build().unwrap().block
			},
			false,
			false,
			true,
			ForkChoiceStrategy::LongestChain,
		)
		.pop()
		.unwrap();
	// at block 27 of the fork add an authority transition
	peer.generate_blocks_at(
		BlockId::Hash(hash),
		1,
		BlockOrigin::File,
		edit_block,
		false,
		false,
		true,
		ForkChoiceStrategy::LongestChain,
	);

	// Fork after revert point

	// add more block on top of block 25 (until we have 28)
	let hash = peer
		.generate_blocks_at(
			BlockId::Number(25),
			3,
			BlockOrigin::File,
			|mut builder| {
				builder.push_deposit_log_digest_item(DigestItem::Other(vec![2])).unwrap();
				builder.build().unwrap().block
			},
			false,
			false,
			true,
			ForkChoiceStrategy::LongestChain,
		)
		.pop()
		.unwrap();
	// at block 29 of the fork add an authority transition
	peer.generate_blocks_at(
		BlockId::Hash(hash),
		1,
		BlockOrigin::File,
		edit_block,
		false,
		false,
		true,
		ForkChoiceStrategy::LongestChain,
	);

	revert(client.clone(), 6).unwrap();

	let persistent_data: PersistentData<Block> = aux_schema::load_persistent(
		&*client,
		client.info().genesis_hash,
		Zero::zero(),
		|| unreachable!(),
	)
	.unwrap();
	let changes_num: Vec<_> = persistent_data
		.authority_set
		.inner()
		.pending_standard_changes
		.iter()
		.map(|(_, n, _)| *n)
		.collect();
	assert_eq!(changes_num, [21, 27]);
}
