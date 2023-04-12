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

//! Tests and test helpers for BEEFY.

use crate::{
	aux_schema::{load_persistent, tests::verify_persisted_version},
	beefy_block_import_and_links,
	communication::{
		gossip::{
			proofs_topic, tests::sign_commitment, votes_topic, GossipFilterCfg, GossipMessage,
			GossipValidator,
		},
		request_response::{on_demand_justifications_protocol_config, BeefyJustifsRequestHandler},
	},
	gossip_protocol_name,
	justification::*,
	load_or_init_voter_state, wait_for_runtime_pallet, BeefyRPCLinks, BeefyVoterLinks, KnownPeers,
	PersistedState,
};
use futures::{future, stream::FuturesUnordered, Future, FutureExt, StreamExt};
use parking_lot::Mutex;
use sc_client_api::{Backend as BackendT, BlockchainEvents, FinalityNotifications, HeaderBackend};
use sc_consensus::{
	BlockImport, BlockImportParams, BoxJustificationImport, ForkChoiceStrategy, ImportResult,
	ImportedAux,
};
use sc_network::{config::RequestResponseConfig, ProtocolName};
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	PeersFullClient, TestNetFactory,
};
use sc_utils::notification::NotificationReceiver;
use serde::{Deserialize, Serialize};
use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_consensus::BlockOrigin;
use sp_consensus_beefy::{
	crypto::{AuthorityId, Signature},
	known_payloads,
	mmr::{find_mmr_root_digest, MmrRootProvider},
	BeefyApi, Commitment, ConsensusLog, EquivocationProof, Keyring as BeefyKeyring, MmrRootHash,
	OpaqueKeyOwnershipProof, Payload, SignedCommitment, ValidatorSet, ValidatorSetId,
	VersionedFinalityProof, VoteMessage, BEEFY_ENGINE_ID, KEY_TYPE as BeefyKeyType,
};
use sp_core::H256;
use sp_keystore::{testing::MemoryKeystore, Keystore, KeystorePtr};
use sp_mmr_primitives::{Error as MmrError, MmrApi};
use sp_runtime::{
	codec::{Decode, Encode},
	traits::{Header as HeaderT, NumberFor},
	BuildStorage, DigestItem, EncodedJustification, Justifications, Storage,
};
use std::{marker::PhantomData, sync::Arc, task::Poll};
use substrate_test_runtime_client::{runtime::Header, ClientExt};
use tokio::time::Duration;

const GENESIS_HASH: H256 = H256::zero();
fn beefy_gossip_proto_name() -> ProtocolName {
	gossip_protocol_name(GENESIS_HASH, None)
}

const GOOD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0xbf);
const BAD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0x42);
const ALTERNATE_BAD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0x13);

type BeefyBlockImport = crate::BeefyBlockImport<
	Block,
	substrate_test_runtime_client::Backend,
	TestApi,
	BlockImportAdapter<PeersClient, sp_api::TransactionFor<TestApi, Block>>,
>;

pub(crate) type BeefyValidatorSet = ValidatorSet<AuthorityId>;
pub(crate) type BeefyPeer = Peer<PeerData, BeefyBlockImport>;

#[derive(Debug, Serialize, Deserialize)]
struct Genesis(std::collections::BTreeMap<String, String>);
impl BuildStorage for Genesis {
	fn assimilate_storage(&self, storage: &mut Storage) -> Result<(), String> {
		storage
			.top
			.extend(self.0.iter().map(|(a, b)| (a.clone().into_bytes(), b.clone().into_bytes())));
		Ok(())
	}
}

#[derive(Default)]
pub(crate) struct PeerData {
	pub(crate) beefy_rpc_links: Mutex<Option<BeefyRPCLinks<Block>>>,
	pub(crate) beefy_voter_links: Mutex<Option<BeefyVoterLinks<Block>>>,
	pub(crate) beefy_justif_req_handler:
		Mutex<Option<BeefyJustifsRequestHandler<Block, PeersFullClient>>>,
}

#[derive(Default)]
pub(crate) struct BeefyTestNet {
	peers: Vec<BeefyPeer>,
	pub beefy_genesis: NumberFor<Block>,
}

impl BeefyTestNet {
	pub(crate) fn new(n_authority: usize) -> Self {
		let beefy_genesis = 1;
		let mut net = BeefyTestNet { peers: Vec::with_capacity(n_authority), beefy_genesis };

		for i in 0..n_authority {
			let (rx, cfg) = on_demand_justifications_protocol_config(GENESIS_HASH, None);
			let justif_protocol_name = cfg.name.clone();

			net.add_authority_peer(vec![cfg]);

			let client = net.peers[i].client().as_client();
			let justif_handler = BeefyJustifsRequestHandler {
				request_receiver: rx,
				justif_protocol_name,
				client,
				_block: PhantomData,
				metrics: None,
			};
			*net.peers[i].data.beefy_justif_req_handler.lock() = Some(justif_handler);
		}
		net
	}

	pub(crate) fn add_authority_peer(&mut self, req_resp_cfgs: Vec<RequestResponseConfig>) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![beefy_gossip_proto_name()],
			request_response_protocols: req_resp_cfgs,
			is_authority: true,
			..Default::default()
		});
	}

	/// Builds the blocks and returns the vector of built block hashes.
	/// Returned vector contains the genesis hash which allows for easy indexing (block number is
	/// equal to index)
	pub(crate) async fn generate_blocks_and_sync(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet,
		include_mmr_digest: bool,
	) -> Vec<H256> {
		let mut all_hashes = Vec::with_capacity(count + 1);

		// make sure genesis is the only block in network, so we can insert genesis at the beginning
		// of hashes, otherwise indexing would be broken
		assert!(self.peer(0).client().as_backend().blockchain().hash(1).unwrap().is_none());

		// push genesis to make indexing human readable (index equals to block number)
		all_hashes.push(self.peer(0).client().info().genesis_hash);

		let built_hashes = self.peer(0).generate_blocks(count, BlockOrigin::File, |builder| {
			let mut block = builder.build().unwrap().block;

			if include_mmr_digest {
				let block_num = *block.header.number();
				let num_byte = block_num.to_le_bytes().into_iter().next().unwrap();
				let mmr_root = MmrRootHash::repeat_byte(num_byte);
				add_mmr_digest(&mut block.header, mmr_root);
			}

			if *block.header.number() % session_length == 0 {
				add_auth_change_digest(&mut block.header, validator_set.clone());
			}

			block
		});
		all_hashes.extend(built_hashes);
		self.run_until_sync().await;

		all_hashes
	}
}

impl TestNetFactory for BeefyTestNet {
	type Verifier = PassThroughVerifier;
	type BlockImport = BeefyBlockImport;
	type PeerData = PeerData;

	fn make_verifier(&self, _client: PeersClient, _: &PeerData) -> Self::Verifier {
		PassThroughVerifier::new(false) // use non-instant finality.
	}

	fn make_block_import(
		&self,
		client: PeersClient,
	) -> (
		BlockImportAdapter<Self::BlockImport>,
		Option<BoxJustificationImport<Block>>,
		Self::PeerData,
	) {
		let keys = &[BeefyKeyring::Alice, BeefyKeyring::Bob];
		let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
		let api = Arc::new(TestApi::new(self.beefy_genesis, &validator_set, GOOD_MMR_ROOT));
		let inner = BlockImportAdapter::new(client.clone());
		let (block_import, voter_links, rpc_links) =
			beefy_block_import_and_links(inner, client.as_backend(), api, None);
		let peer_data = PeerData {
			beefy_rpc_links: Mutex::new(Some(rpc_links)),
			beefy_voter_links: Mutex::new(Some(voter_links)),
			..Default::default()
		};
		(BlockImportAdapter::new(block_import), None, peer_data)
	}

	fn peer(&mut self, i: usize) -> &mut BeefyPeer {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<BeefyPeer> {
		&self.peers
	}

	fn peers_mut(&mut self) -> &mut Vec<BeefyPeer> {
		&mut self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<BeefyPeer>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}

	fn add_full_peer(&mut self) {
		// `add_authority_peer()` used instead.
		unimplemented!()
	}
}

#[derive(Clone)]
pub(crate) struct TestApi {
	pub beefy_genesis: u64,
	pub validator_set: BeefyValidatorSet,
	pub mmr_root_hash: MmrRootHash,
	pub reported_equivocations:
		Option<Arc<Mutex<Vec<EquivocationProof<NumberFor<Block>, AuthorityId, Signature>>>>>,
}

impl TestApi {
	pub fn new(
		beefy_genesis: u64,
		validator_set: &BeefyValidatorSet,
		mmr_root_hash: MmrRootHash,
	) -> Self {
		TestApi {
			beefy_genesis,
			validator_set: validator_set.clone(),
			mmr_root_hash,
			reported_equivocations: None,
		}
	}

	pub fn with_validator_set(validator_set: &BeefyValidatorSet) -> Self {
		TestApi {
			beefy_genesis: 1,
			validator_set: validator_set.clone(),
			mmr_root_hash: GOOD_MMR_ROOT,
			reported_equivocations: None,
		}
	}

	pub fn allow_equivocations(&mut self) {
		self.reported_equivocations = Some(Arc::new(Mutex::new(vec![])));
	}
}

// compiler gets confused and warns us about unused inner
#[allow(dead_code)]
pub(crate) struct RuntimeApi {
	inner: TestApi,
}

impl ProvideRuntimeApi<Block> for TestApi {
	type Api = RuntimeApi;
	fn runtime_api(&self) -> ApiRef<Self::Api> {
		RuntimeApi { inner: self.clone() }.into()
	}
}
sp_api::mock_impl_runtime_apis! {
	impl BeefyApi<Block> for RuntimeApi {
		fn beefy_genesis() -> Option<NumberFor<Block>> {
			Some(self.inner.beefy_genesis)
		}

		fn validator_set() -> Option<BeefyValidatorSet> {
			Some(self.inner.validator_set.clone())
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			proof: EquivocationProof<NumberFor<Block>, AuthorityId, Signature>,
			_dummy: OpaqueKeyOwnershipProof,
		) -> Option<()> {
			if let Some(equivocations_buf) = self.inner.reported_equivocations.as_ref() {
				equivocations_buf.lock().push(proof);
				None
			} else {
				panic!("Equivocations not expected, but following proof was reported: {:?}", proof);
			}
		}

		fn generate_key_ownership_proof(
			_dummy1: ValidatorSetId,
			_dummy2: AuthorityId,
		) -> Option<OpaqueKeyOwnershipProof> { Some(OpaqueKeyOwnershipProof::new(vec![])) }
	}

	impl MmrApi<Block, MmrRootHash, NumberFor<Block>> for RuntimeApi {
		fn mmr_root() -> Result<MmrRootHash, MmrError> {
			Ok(self.inner.mmr_root_hash)
		}
	}
}

fn add_mmr_digest(header: &mut Header, mmr_hash: MmrRootHash) {
	header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthorityId>::MmrRoot(mmr_hash).encode(),
	));
}

fn add_auth_change_digest(header: &mut Header, new_auth_set: BeefyValidatorSet) {
	header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthorityId>::AuthoritiesChange(new_auth_set).encode(),
	));
}

pub(crate) fn make_beefy_ids(keys: &[BeefyKeyring]) -> Vec<AuthorityId> {
	keys.iter().map(|&key| key.public().into()).collect()
}

pub(crate) fn create_beefy_keystore(authority: BeefyKeyring) -> KeystorePtr {
	let keystore = MemoryKeystore::new();
	keystore
		.ecdsa_generate_new(BeefyKeyType, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore.into()
}

async fn voter_init_setup(
	net: &mut BeefyTestNet,
	finality: &mut futures::stream::Fuse<FinalityNotifications<Block>>,
	api: &TestApi,
) -> sp_blockchain::Result<PersistedState<Block>> {
	let backend = net.peer(0).client().as_backend();
	let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
	let (gossip_validator, _) = GossipValidator::new(known_peers);
	let gossip_validator = Arc::new(gossip_validator);
	let mut gossip_engine = sc_network_gossip::GossipEngine::new(
		net.peer(0).network_service().clone(),
		net.peer(0).sync_service().clone(),
		"/beefy/whatever",
		gossip_validator,
		None,
	);
	let best_grandpa = wait_for_runtime_pallet(api, &mut gossip_engine, finality).await.unwrap();
	load_or_init_voter_state(&*backend, api, best_grandpa, 1)
}

// Spawns beefy voters. Returns a future to spawn on the runtime.
fn initialize_beefy<API>(
	net: &mut BeefyTestNet,
	peers: Vec<(usize, &BeefyKeyring, Arc<API>)>,
	min_block_delta: u32,
) -> impl Future<Output = ()>
where
	API: ProvideRuntimeApi<Block> + Sync + Send,
	API::Api: BeefyApi<Block> + MmrApi<Block, MmrRootHash, NumberFor<Block>>,
{
	let tasks = FuturesUnordered::new();

	for (peer_id, key, api) in peers.into_iter() {
		let peer = &net.peers[peer_id];

		let keystore = create_beefy_keystore(*key);

		let (_, _, peer_data) = net.make_block_import(peer.client().clone());
		let PeerData { beefy_rpc_links, beefy_voter_links, .. } = peer_data;

		let beefy_voter_links = beefy_voter_links.lock().take();
		*peer.data.beefy_rpc_links.lock() = beefy_rpc_links.lock().take();
		*peer.data.beefy_voter_links.lock() = beefy_voter_links.clone();

		let on_demand_justif_handler = peer.data.beefy_justif_req_handler.lock().take().unwrap();

		let network_params = crate::BeefyNetworkParams {
			network: peer.network_service().clone(),
			sync: peer.sync_service().clone(),
			gossip_protocol_name: beefy_gossip_proto_name(),
			justifications_protocol_name: on_demand_justif_handler.protocol_name(),
			_phantom: PhantomData,
		};
		let payload_provider = MmrRootProvider::new(api.clone());

		let beefy_params = crate::BeefyParams {
			client: peer.client().as_client(),
			backend: peer.client().as_backend(),
			payload_provider,
			runtime: api.clone(),
			key_store: Some(keystore),
			network_params,
			links: beefy_voter_links.unwrap(),
			min_block_delta,
			prometheus_registry: None,
			on_demand_justifications_handler: on_demand_justif_handler,
		};
		let task = crate::start_beefy_gadget::<_, _, _, _, _, _, _>(beefy_params);

		fn assert_send<T: Send>(_: &T) {}
		assert_send(&task);
		tasks.push(task);
	}

	tasks.for_each(|_| async move {})
}

async fn run_until(future: impl Future + Unpin, net: &Arc<Mutex<BeefyTestNet>>) {
	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	let _ = future::select(future, drive_to_completion).await;
}

async fn run_for(duration: Duration, net: &Arc<Mutex<BeefyTestNet>>) {
	run_until(Box::pin(tokio::time::sleep(duration)), net).await;
}

pub(crate) fn get_beefy_streams(
	net: &mut BeefyTestNet,
	// peer index and key
	peers: impl Iterator<Item = (usize, BeefyKeyring)>,
) -> (Vec<NotificationReceiver<H256>>, Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block>>>)
{
	let mut best_block_streams = Vec::new();
	let mut versioned_finality_proof_streams = Vec::new();
	peers.for_each(|(index, _)| {
		let beefy_rpc_links = net.peer(index).data.beefy_rpc_links.lock().clone().unwrap();
		let BeefyRPCLinks { from_voter_justif_stream, from_voter_best_beefy_stream } =
			beefy_rpc_links;
		best_block_streams.push(from_voter_best_beefy_stream.subscribe(100_000));
		versioned_finality_proof_streams.push(from_voter_justif_stream.subscribe(100_000));
	});
	(best_block_streams, versioned_finality_proof_streams)
}

async fn wait_for_best_beefy_blocks(
	streams: Vec<NotificationReceiver<H256>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	expected_beefy_blocks: &[u64],
) {
	let mut wait_for = Vec::new();
	let len = expected_beefy_blocks.len();
	streams.into_iter().enumerate().for_each(|(i, stream)| {
		let mut expected = expected_beefy_blocks.iter();
		wait_for.push(Box::pin(stream.take(len).for_each(move |best_beefy_hash| {
			let expected = expected.next();
			async move {
				let header =
					net.lock().peer(i).client().as_client().expect_header(best_beefy_hash).unwrap();
				let best_beefy = *header.number();

				assert_eq!(expected, Some(best_beefy).as_ref());
			}
		})));
	});
	let wait_for = futures::future::join_all(wait_for);
	run_until(wait_for, net).await;
}

async fn wait_for_beefy_signed_commitments(
	streams: Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block>>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	expected_commitment_block_nums: &[u64],
) {
	let mut wait_for = Vec::new();
	let len = expected_commitment_block_nums.len();
	streams.into_iter().for_each(|stream| {
		let mut expected = expected_commitment_block_nums.iter();
		wait_for.push(Box::pin(stream.take(len).for_each(move |versioned_finality_proof| {
			let expected = expected.next();
			async move {
				let signed_commitment = match versioned_finality_proof {
					sp_consensus_beefy::VersionedFinalityProof::V1(sc) => sc,
				};
				let commitment_block_num = signed_commitment.commitment.block_number;
				assert_eq!(expected, Some(commitment_block_num).as_ref());
				// TODO: also verify commitment payload, validator set id, and signatures.
			}
		})));
	});
	let wait_for = futures::future::join_all(wait_for);
	run_until(wait_for, net).await;
}

async fn streams_empty_after_future<T>(
	streams: Vec<NotificationReceiver<T>>,
	future: Option<impl Future + Unpin>,
) where
	T: std::fmt::Debug,
	T: std::cmp::PartialEq,
{
	if let Some(future) = future {
		future.await;
	}
	for mut stream in streams.into_iter() {
		future::poll_fn(move |cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}
}

async fn streams_empty_after_timeout<T>(
	streams: Vec<NotificationReceiver<T>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	timeout: Option<Duration>,
) where
	T: std::fmt::Debug,
	T: std::cmp::PartialEq,
{
	let timeout = timeout.map(|timeout| Box::pin(run_for(timeout, net)));
	streams_empty_after_future(streams, timeout).await;
}

async fn finalize_block_and_wait_for_beefy(
	net: &Arc<Mutex<BeefyTestNet>>,
	// peer index and key
	peers: impl Iterator<Item = (usize, BeefyKeyring)> + Clone,
	finalize_target: &H256,
	expected_beefy: &[u64],
) {
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());

	peers.clone().for_each(|(index, _)| {
		let client = net.lock().peer(index).client().as_client();
		client.finalize_block(*finalize_target, None).unwrap();
	});

	if expected_beefy.is_empty() {
		// run for quarter second then verify no new best beefy block available
		let timeout = Some(Duration::from_millis(250));
		streams_empty_after_timeout(best_blocks, &net, timeout).await;
		streams_empty_after_timeout(versioned_finality_proof, &net, None).await;
	} else {
		// run until expected beefy blocks are received
		wait_for_best_beefy_blocks(best_blocks, &net, expected_beefy).await;
		wait_for_beefy_signed_commitments(versioned_finality_proof, &net, expected_beefy).await;
	}
}

#[tokio::test]
async fn beefy_finalizing_blocks() {
	sp_tracing::try_init_simple();

	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
	let session_len = 10;
	let min_block_delta = 4;

	let mut net = BeefyTestNet::new(2);

	let api = Arc::new(TestApi::with_validator_set(&validator_set));
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	let hashes = net.generate_blocks_and_sync(42, session_len, &validator_set, true).await;

	let net = Arc::new(Mutex::new(net));

	// Minimum BEEFY block delta is 4.

	let peers = peers.into_iter().enumerate();
	// finalize block #5 -> BEEFY should finalize #1 (mandatory) and #5 from diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[1], &[1]).await;
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[5], &[5]).await;

	// GRANDPA finalize #10 -> BEEFY finalize #10 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[10], &[10]).await;

	// GRANDPA finalize #18 -> BEEFY finalize #14, then #18 (diff-power-of-two rule)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[18], &[14, 18]).await;

	// GRANDPA finalize #20 -> BEEFY finalize #20 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[20], &[20]).await;

	// GRANDPA finalize #21 -> BEEFY finalize nothing (yet) because min delta is 4
	finalize_block_and_wait_for_beefy(&net, peers, &hashes[21], &[]).await;
}

#[tokio::test]
async fn lagging_validators() {
	sp_tracing::try_init_simple();

	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie];
	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
	let session_len = 30;
	let min_block_delta = 1;

	let mut net = BeefyTestNet::new(3);
	let api = Arc::new(TestApi::with_validator_set(&validator_set));
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	// push 62 blocks including `AuthorityChange` digests every 30 blocks.
	let hashes = net.generate_blocks_and_sync(62, session_len, &validator_set, true).await;

	let net = Arc::new(Mutex::new(net));

	let peers = peers.into_iter().enumerate();
	// finalize block #15 -> BEEFY should finalize #1 (mandatory) and #9, #13, #14, #15 from
	// diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[1], &[1]).await;
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[15], &[9, 13, 14, 15]).await;

	// Alice and Bob finalize #25, Charlie lags behind
	let finalize = hashes[25];
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(100));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// Charlie catches up and also finalizes #25
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(2).client().as_client().finalize_block(finalize, None).unwrap();
	// expected beefy finalizes blocks 23, 24, 25 from diff-power-of-two
	wait_for_best_beefy_blocks(best_blocks, &net, &[23, 24, 25]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[23, 24, 25]).await;

	// Both finalize #30 (mandatory session) and #32 -> BEEFY finalize #30 (mandatory), #31, #32
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[30], &[30]).await;
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[32], &[31, 32]).await;

	// Verify that session-boundary votes get buffered by client and only processed once
	// session-boundary block is GRANDPA-finalized (this guarantees authenticity for the new session
	// validator set).

	// Alice and Bob finalize session-boundary mandatory block #60, Charlie lags behind
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	let finalize = hashes[60];
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(100));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// Charlie catches up and also finalizes #60 (and should have buffered Alice's vote on #60)
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	net.lock().peer(2).client().as_client().finalize_block(finalize, None).unwrap();
	// verify beefy skips intermediary votes, and successfully finalizes mandatory block #60
	wait_for_best_beefy_blocks(best_blocks, &net, &[60]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[60]).await;
}

#[tokio::test]
async fn correct_beefy_payload() {
	sp_tracing::try_init_simple();

	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie, BeefyKeyring::Dave];
	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
	let session_len = 20;
	let min_block_delta = 2;

	let mut net = BeefyTestNet::new(4);

	// Alice, Bob, Charlie will vote on good payloads
	let good_api = Arc::new(TestApi::new(1, &validator_set, GOOD_MMR_ROOT));
	let good_peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie]
		.iter()
		.enumerate()
		.map(|(id, key)| (id, key, good_api.clone()))
		.collect();
	tokio::spawn(initialize_beefy(&mut net, good_peers, min_block_delta));

	// Dave will vote on bad mmr roots
	let bad_api = Arc::new(TestApi::new(1, &validator_set, BAD_MMR_ROOT));
	let bad_peers = vec![(3, &BeefyKeyring::Dave, bad_api)];
	tokio::spawn(initialize_beefy(&mut net, bad_peers, min_block_delta));

	// push 12 blocks
	let hashes = net.generate_blocks_and_sync(12, session_len, &validator_set, false).await;

	let net = Arc::new(Mutex::new(net));
	let peers = peers.into_iter().enumerate();
	// with 3 good voters and 1 bad one, consensus should happen and best blocks produced.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[1], &[1]).await;
	finalize_block_and_wait_for_beefy(&net, peers, &hashes[10], &[9]).await;

	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), [(0, BeefyKeyring::Alice)].into_iter());

	// now 2 good validators and 1 bad one are voting
	let hashof11 = hashes[11];
	net.lock().peer(0).client().as_client().finalize_block(hashof11, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(hashof11, None).unwrap();
	net.lock().peer(3).client().as_client().finalize_block(hashof11, None).unwrap();

	// verify consensus is _not_ reached
	let timeout = Some(Duration::from_millis(100));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// 3rd good validator catches up and votes as well
	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), [(0, BeefyKeyring::Alice)].into_iter());
	net.lock().peer(2).client().as_client().finalize_block(hashof11, None).unwrap();

	// verify consensus is reached
	wait_for_best_beefy_blocks(best_blocks, &net, &[11]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[11]).await;
}

#[tokio::test]
async fn beefy_importing_justifications() {
	use futures::{future::poll_fn, task::Poll};
	use sc_block_builder::BlockBuilderProvider;
	use sc_client_api::BlockBackend;

	sp_tracing::try_init_simple();

	let mut net = BeefyTestNet::new(2);
	let keys = &[BeefyKeyring::Alice, BeefyKeyring::Bob];
	let good_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	// Set BEEFY genesis to block 3.
	net.beefy_genesis = 3;

	let client = net.peer(0).client().clone();
	let full_client = client.as_client();
	let (mut block_import, _, peer_data) = net.make_block_import(client.clone());
	let PeerData { beefy_voter_links, .. } = peer_data;
	let justif_stream = beefy_voter_links.lock().take().unwrap().from_block_import_justif_stream;
	let mut justif_recv = justif_stream.subscribe(100_000);

	let params = |block: Block, justifications: Option<Justifications>| {
		let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
		import.justifications = justifications;
		import.body = Some(block.extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		import
	};
	let backend_justif_for = |block_hash: H256| -> Option<EncodedJustification> {
		full_client
			.justifications(block_hash)
			.unwrap()
			.and_then(|j| j.get(BEEFY_ENGINE_ID).cloned())
	};

	let builder = full_client
		.new_block_at(full_client.chain_info().genesis_hash, Default::default(), false)
		.unwrap();
	let block = builder.build().unwrap().block;
	let hashof1 = block.header.hash();

	// Import block 1 without justifications.
	assert_eq!(
		block_import.import_block(params(block.clone(), None)).await.unwrap(),
		ImportResult::Imported(ImportedAux { is_new_best: true, ..Default::default() }),
	);
	assert_eq!(
		block_import.import_block(params(block, None)).await.unwrap(),
		ImportResult::AlreadyInChain,
	);

	// Import block 2 with "valid" justification (beefy pallet genesis block not yet reached).
	let block_num = 2;
	let builder = full_client.new_block_at(hashof1, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof2 = block.header.hash();

	let proof = crate::justification::tests::new_finality_proof(block_num, &good_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));
	assert_eq!(
		block_import.import_block(params(block, justif)).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);

	// Verify no BEEFY justifications present (for either block 1 or 2):
	{
		// none in backend,
		assert_eq!(backend_justif_for(hashof1), None);
		assert_eq!(backend_justif_for(hashof2), None);
		// and none sent to BEEFY worker.
		poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}

	// Import block 3 with valid justification.
	let block_num = 3;
	let builder = full_client.new_block_at(hashof2, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof3 = block.header.hash();
	let proof = crate::justification::tests::new_finality_proof(block_num, &good_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));
	let mut justif_recv = justif_stream.subscribe(100_000);
	assert_eq!(
		block_import.import_block(params(block, justif)).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);
	// Verify BEEFY justification successfully imported:
	{
		// still not in backend (worker is responsible for appending to backend),
		assert_eq!(backend_justif_for(hashof3), None);
		// but sent to BEEFY worker
		// (worker will append it to backend when all previous mandatory justifs are there as well).
		poll_fn(move |cx| {
			match justif_recv.poll_next_unpin(cx) {
				Poll::Ready(Some(_justification)) => (),
				v => panic!("unexpected value: {:?}", v),
			}
			Poll::Ready(())
		})
		.await;
	}

	// Import block 4 with invalid justification (incorrect validator set).
	let block_num = 4;
	let builder = full_client.new_block_at(hashof3, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof4 = block.header.hash();
	let keys = &[BeefyKeyring::Alice];
	let bad_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();
	let proof = crate::justification::tests::new_finality_proof(block_num, &bad_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));
	let mut justif_recv = justif_stream.subscribe(100_000);
	assert_eq!(
		block_import.import_block(params(block, justif)).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			// Still `false` because we don't want to fail import on bad BEEFY justifications.
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);
	// Verify bad BEEFY justifications was not imported:
	{
		// none in backend,
		assert_eq!(backend_justif_for(hashof4), None);
		// and none sent to BEEFY worker.
		poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}
}

#[tokio::test]
async fn on_demand_beefy_justification_sync() {
	sp_tracing::try_init_simple();

	let all_peers =
		[BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie, BeefyKeyring::Dave];
	let validator_set = ValidatorSet::new(make_beefy_ids(&all_peers), 0).unwrap();
	let session_len = 5;
	let min_block_delta = 4;

	let mut net = BeefyTestNet::new(4);

	// Alice, Bob, Charlie start first and make progress through voting.
	let api = Arc::new(TestApi::with_validator_set(&validator_set));
	let fast_peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie];
	let voting_peers =
		fast_peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy(&mut net, voting_peers, min_block_delta));

	// Dave will start late and have to catch up using on-demand justification requests (since
	// in this test there is no block import queue to automatically import justifications).
	let dave = vec![(3, &BeefyKeyring::Dave, api)];
	// Instantiate but don't run Dave, yet.
	let dave_task = initialize_beefy(&mut net, dave, min_block_delta);
	let dave_index = 3;

	// push 30 blocks
	let mut hashes = net.generate_blocks_and_sync(30, session_len, &validator_set, false).await;

	let fast_peers = fast_peers.into_iter().enumerate();
	let net = Arc::new(Mutex::new(net));
	// With 3 active voters and one inactive, consensus should happen and blocks BEEFY-finalized.
	// Need to finalize at least one block in each session, choose randomly.
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[1], &[1]).await;
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[6], &[5]).await;
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[10], &[10]).await;
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[17], &[15]).await;
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[24], &[20]).await;

	// Spawn Dave, they are now way behind voting and can only catch up through on-demand justif
	// sync.
	tokio::spawn(dave_task);
	// Dave pushes and syncs 4 more blocks just to make sure he gets included in gossip.
	{
		let mut net_guard = net.lock();
		let built_hashes =
			net_guard
				.peer(dave_index)
				.generate_blocks(4, BlockOrigin::File, |builder| builder.build().unwrap().block);
		hashes.extend(built_hashes);
		net_guard.run_until_sync().await;
	}

	let (dave_best_blocks, _) =
		get_beefy_streams(&mut net.lock(), [(dave_index, BeefyKeyring::Dave)].into_iter());
	let client = net.lock().peer(dave_index).client().as_client();
	client.finalize_block(hashes[1], None).unwrap();
	// Give Dave task some cpu cycles to process the finality notification,
	run_for(Duration::from_millis(100), &net).await;
	// freshly spun up Dave now needs to listen for gossip to figure out the state of their peers.

	// Have the other peers do some gossip so Dave finds out about their progress.
	finalize_block_and_wait_for_beefy(&net, fast_peers.clone(), &hashes[25], &[25]).await;
	finalize_block_and_wait_for_beefy(&net, fast_peers, &hashes[29], &[29]).await;

	// Kick Dave's async loop by finalizing another block.
	client.finalize_block(hashes[2], None).unwrap();

	// And verify Dave successfully finalized #1 (through on-demand justification request).
	wait_for_best_beefy_blocks(dave_best_blocks, &net, &[1]).await;

	// Give all tasks some cpu cycles to burn through their events queues,
	run_for(Duration::from_millis(100), &net).await;
	// then verify Dave catches up through on-demand justification requests.
	let (dave_best_blocks, _) =
		get_beefy_streams(&mut net.lock(), [(dave_index, BeefyKeyring::Dave)].into_iter());
	client.finalize_block(hashes[6], None).unwrap();
	client.finalize_block(hashes[10], None).unwrap();
	client.finalize_block(hashes[17], None).unwrap();
	client.finalize_block(hashes[24], None).unwrap();
	client.finalize_block(hashes[26], None).unwrap();
	wait_for_best_beefy_blocks(dave_best_blocks, &net, &[5, 10, 15, 20, 25]).await;
}

#[tokio::test]
async fn should_initialize_voter_at_genesis() {
	let keys = &[BeefyKeyring::Alice];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	let mut net = BeefyTestNet::new(1);
	let backend = net.peer(0).client().as_backend();

	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	let hashes = net.generate_blocks_and_sync(15, 10, &validator_set, false).await;

	let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

	// finalize 13 without justifications
	net.peer(0).client().as_client().finalize_block(hashes[13], None).unwrap();

	let api = TestApi::with_validator_set(&validator_set);
	// load persistent state - nothing in DB, should init at genesis
	let persisted_state = voter_init_setup(&mut net, &mut finality, &api).await.unwrap();

	// Test initialization at session boundary.
	// verify voter initialized with two sessions starting at blocks 1 and 10
	let sessions = persisted_state.voting_oracle().sessions();
	assert_eq!(sessions.len(), 2);
	assert_eq!(sessions[0].session_start(), 1);
	assert_eq!(sessions[1].session_start(), 10);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), 1);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify next vote target is mandatory block 1
	assert_eq!(persisted_state.best_beefy_block(), 0);
	assert_eq!(persisted_state.best_grandpa_number(), 13);
	assert_eq!(persisted_state.voting_oracle().voting_target(), Some(1));

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn should_initialize_voter_at_custom_genesis() {
	let keys = &[BeefyKeyring::Alice];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	let mut net = BeefyTestNet::new(1);
	let backend = net.peer(0).client().as_backend();
	// custom pallet genesis is block number 7
	let custom_pallet_genesis = 7;
	let api = TestApi::new(custom_pallet_genesis, &validator_set, GOOD_MMR_ROOT);

	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	let hashes = net.generate_blocks_and_sync(15, 10, &validator_set, false).await;

	let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

	// finalize 3, 5, 8 without justifications
	net.peer(0).client().as_client().finalize_block(hashes[3], None).unwrap();
	net.peer(0).client().as_client().finalize_block(hashes[5], None).unwrap();
	net.peer(0).client().as_client().finalize_block(hashes[8], None).unwrap();

	// load persistent state - nothing in DB, should init at genesis
	let persisted_state = voter_init_setup(&mut net, &mut finality, &api).await.unwrap();

	// Test initialization at session boundary.
	// verify voter initialized with single session starting at block `custom_pallet_genesis` (7)
	let sessions = persisted_state.voting_oracle().sessions();
	assert_eq!(sessions.len(), 1);
	assert_eq!(sessions[0].session_start(), custom_pallet_genesis);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), custom_pallet_genesis);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify next vote target is mandatory block 7
	assert_eq!(persisted_state.best_beefy_block(), 0);
	assert_eq!(persisted_state.best_grandpa_number(), 8);
	assert_eq!(persisted_state.voting_oracle().voting_target(), Some(custom_pallet_genesis));

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn should_initialize_voter_when_last_final_is_session_boundary() {
	let keys = &[BeefyKeyring::Alice];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	let mut net = BeefyTestNet::new(1);
	let backend = net.peer(0).client().as_backend();

	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	let hashes = net.generate_blocks_and_sync(15, 10, &validator_set, false).await;

	let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

	// finalize 13 without justifications
	net.peer(0).client().as_client().finalize_block(hashes[13], None).unwrap();

	// import/append BEEFY justification for session boundary block 10
	let commitment = Commitment {
		payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
		block_number: 10,
		validator_set_id: validator_set.id(),
	};
	let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
		commitment,
		signatures: vec![None],
	});
	backend
		.append_justification(hashes[10], (BEEFY_ENGINE_ID, justif.encode()))
		.unwrap();

	// Test corner-case where session boundary == last beefy finalized,
	// expect rounds initialized at last beefy finalized 10.

	let api = TestApi::with_validator_set(&validator_set);
	// load persistent state - nothing in DB, should init at session boundary
	let persisted_state = voter_init_setup(&mut net, &mut finality, &api).await.unwrap();

	// verify voter initialized with single session starting at block 10
	assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), 10);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify block 10 is correctly marked as finalized
	assert_eq!(persisted_state.best_beefy_block(), 10);
	assert_eq!(persisted_state.best_grandpa_number(), 13);
	// verify next vote target is diff-power-of-two block 12
	assert_eq!(persisted_state.voting_oracle().voting_target(), Some(12));

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn should_initialize_voter_at_latest_finalized() {
	let keys = &[BeefyKeyring::Alice];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	let mut net = BeefyTestNet::new(1);
	let backend = net.peer(0).client().as_backend();

	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	let hashes = net.generate_blocks_and_sync(15, 10, &validator_set, false).await;

	let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

	// finalize 13 without justifications
	net.peer(0).client().as_client().finalize_block(hashes[13], None).unwrap();

	// import/append BEEFY justification for block 12
	let commitment = Commitment {
		payload: Payload::from_single_entry(known_payloads::MMR_ROOT_ID, vec![]),
		block_number: 12,
		validator_set_id: validator_set.id(),
	};
	let justif = VersionedFinalityProof::<_, Signature>::V1(SignedCommitment {
		commitment,
		signatures: vec![None],
	});
	backend
		.append_justification(hashes[12], (BEEFY_ENGINE_ID, justif.encode()))
		.unwrap();

	// Test initialization at last BEEFY finalized.

	let api = TestApi::with_validator_set(&validator_set);
	// load persistent state - nothing in DB, should init at last BEEFY finalized
	let persisted_state = voter_init_setup(&mut net, &mut finality, &api).await.unwrap();

	// verify voter initialized with single session starting at block 12
	assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), 12);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify next vote target is 13
	assert_eq!(persisted_state.best_beefy_block(), 12);
	assert_eq!(persisted_state.best_grandpa_number(), 13);
	assert_eq!(persisted_state.voting_oracle().voting_target(), Some(13));

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn beefy_finalizing_after_pallet_genesis() {
	sp_tracing::try_init_simple();

	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
	let session_len = 10;
	let min_block_delta = 1;
	let pallet_genesis = 15;

	let mut net = BeefyTestNet::new(2);

	let api = Arc::new(TestApi::new(pallet_genesis, &validator_set, GOOD_MMR_ROOT));
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	let hashes = net.generate_blocks_and_sync(42, session_len, &validator_set, true).await;

	let net = Arc::new(Mutex::new(net));
	let peers = peers.into_iter().enumerate();

	// Minimum BEEFY block delta is 1.

	// GRANDPA finalize blocks leading up to BEEFY pallet genesis -> BEEFY should finalize nothing.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[14], &[]).await;

	// GRANDPA finalize block #16 -> BEEFY should finalize #15 (genesis mandatory) and #16.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[16], &[15, 16]).await;

	// GRANDPA finalize #21 -> BEEFY finalize #20 (mandatory) and #21
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &hashes[21], &[20, 21]).await;
}

#[tokio::test]
async fn beefy_reports_equivocations() {
	sp_tracing::try_init_simple();

	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie];
	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
	let session_len = 10;
	let min_block_delta = 4;

	let mut net = BeefyTestNet::new(3);

	// Alice votes on good MMR roots, equivocations are allowed/expected.
	let mut api_alice = TestApi::with_validator_set(&validator_set);
	api_alice.allow_equivocations();
	let api_alice = Arc::new(api_alice);
	let alice = (0, &BeefyKeyring::Alice, api_alice.clone());
	tokio::spawn(initialize_beefy(&mut net, vec![alice], min_block_delta));

	// Bob votes on bad MMR roots, equivocations are allowed/expected.
	let mut api_bob = TestApi::new(1, &validator_set, BAD_MMR_ROOT);
	api_bob.allow_equivocations();
	let api_bob = Arc::new(api_bob);
	let bob = (1, &BeefyKeyring::Bob, api_bob.clone());
	tokio::spawn(initialize_beefy(&mut net, vec![bob], min_block_delta));

	// We spawn another node voting with Bob key, on alternate bad MMR roots (equivocating).
	// Equivocations are allowed/expected.
	let mut api_bob_prime = TestApi::new(1, &validator_set, ALTERNATE_BAD_MMR_ROOT);
	api_bob_prime.allow_equivocations();
	let api_bob_prime = Arc::new(api_bob_prime);
	let bob_prime = (2, &BeefyKeyring::Bob, api_bob_prime.clone());
	tokio::spawn(initialize_beefy(&mut net, vec![bob_prime], min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	let hashes = net.generate_blocks_and_sync(42, session_len, &validator_set, false).await;

	let net = Arc::new(Mutex::new(net));

	// Minimum BEEFY block delta is 4.

	let peers = peers.into_iter().enumerate();
	// finalize block #1 -> BEEFY should not finalize anything (each node votes on different MMR).
	finalize_block_and_wait_for_beefy(&net, peers, &hashes[1], &[]).await;

	// Verify neither Bob or Bob_Prime report themselves as equivocating.
	assert!(api_bob.reported_equivocations.as_ref().unwrap().lock().is_empty());
	assert!(api_bob_prime.reported_equivocations.as_ref().unwrap().lock().is_empty());

	// Verify Alice reports Bob/Bob_Prime equivocation.
	let alice_reported_equivocations = api_alice.reported_equivocations.as_ref().unwrap().lock();
	assert_eq!(alice_reported_equivocations.len(), 1);
	let equivocation_proof = alice_reported_equivocations.get(0).unwrap();
	assert_eq!(equivocation_proof.first.id, BeefyKeyring::Bob.public());
	assert_eq!(equivocation_proof.first.commitment.block_number, 1);
}

#[tokio::test]
async fn gossipped_finality_proofs() {
	sp_tracing::try_init_simple();

	let validators = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie];
	// Only Alice and Bob are running the voter -> finality threshold not reached
	let peers = [BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(&validators), 0).unwrap();
	let session_len = 30;
	let min_block_delta = 1;

	let mut net = BeefyTestNet::new(3);
	let api = Arc::new(TestApi::with_validator_set(&validator_set));
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();

	let charlie = &net.peers[2];
	let known_peers = Arc::new(Mutex::new(KnownPeers::<Block>::new()));
	// Charlie will run just the gossip engine and not the full voter.
	let (gossip_validator, _) = GossipValidator::new(known_peers);
	let charlie_gossip_validator = Arc::new(gossip_validator);
	charlie_gossip_validator.update_filter(GossipFilterCfg::<Block> {
		start: 1,
		end: 10,
		validator_set: &validator_set,
	});
	let mut charlie_gossip_engine = sc_network_gossip::GossipEngine::new(
		charlie.network_service().clone(),
		charlie.sync_service().clone(),
		beefy_gossip_proto_name(),
		charlie_gossip_validator.clone(),
		None,
	);

	// Alice and Bob run full voter.
	tokio::spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	let net = Arc::new(Mutex::new(net));

	// Pump net + Charlie gossip to see peers.
	let timeout = Box::pin(tokio::time::sleep(Duration::from_millis(200)));
	let gossip_engine_pump = &mut charlie_gossip_engine;
	let pump_with_timeout = future::select(gossip_engine_pump, timeout);
	run_until(pump_with_timeout, &net).await;

	// push 10 blocks
	let hashes = net.lock().generate_blocks_and_sync(10, session_len, &validator_set, true).await;

	let peers = peers.into_iter().enumerate();

	// Alice, Bob and Charlie finalize #1, Alice and Bob vote on it, but not Charlie.
	let finalize = hashes[1];
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(2).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Box::pin(tokio::time::sleep(Duration::from_millis(100)));
	let pump_net = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	let pump_gossip = &mut charlie_gossip_engine;
	let pump_with_timeout = future::select(pump_gossip, future::select(pump_net, timeout));
	streams_empty_after_future(best_blocks, Some(pump_with_timeout)).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	// Charlie gossips finality proof for #1 -> Alice and Bob also finalize.
	let proof = crate::communication::gossip::tests::dummy_proof(1, &validator_set);
	let gossip_proof = GossipMessage::<Block>::FinalityProof(proof);
	let encoded_proof = gossip_proof.encode();
	charlie_gossip_engine.gossip_message(proofs_topic::<Block>(), encoded_proof, true);
	// Expect #1 is finalized.
	wait_for_best_beefy_blocks(best_blocks, &net, &[1]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[1]).await;

	// Code above verifies gossipped finality proofs are correctly imported and consumed by voters.
	// Next, let's verify finality proofs are correctly generated and gossipped by voters.

	// Everyone finalizes #2
	let block_number = 2u64;
	let finalize = hashes[block_number as usize];
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	net.lock().peer(2).client().as_client().finalize_block(finalize, None).unwrap();

	// Simulate Charlie vote on #2
	let header = net.lock().peer(2).client().as_client().expect_header(finalize).unwrap();
	let mmr_root = find_mmr_root_digest::<Block>(&header).unwrap();
	let payload = Payload::from_single_entry(known_payloads::MMR_ROOT_ID, mmr_root.encode());
	let commitment = Commitment { payload, block_number, validator_set_id: validator_set.id() };
	let signature = sign_commitment(&BeefyKeyring::Charlie, &commitment);
	let vote_message = VoteMessage { commitment, id: BeefyKeyring::Charlie.public(), signature };
	let encoded_vote = GossipMessage::<Block>::Vote(vote_message).encode();
	charlie_gossip_engine.gossip_message(votes_topic::<Block>(), encoded_vote, true);

	// Expect #2 is finalized.
	wait_for_best_beefy_blocks(best_blocks, &net, &[2]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[2]).await;

	// Now verify Charlie also sees the gossipped proof generated by either Alice or Bob.
	let mut charlie_gossip_proofs = Box::pin(
		charlie_gossip_engine
			.messages_for(proofs_topic::<Block>())
			.filter_map(|notification| async move {
				GossipMessage::<Block>::decode(&mut &notification.message[..]).ok().and_then(
					|message| match message {
						GossipMessage::<Block>::Vote(_) => unreachable!(),
						GossipMessage::<Block>::FinalityProof(proof) => Some(proof),
					},
				)
			})
			.fuse(),
	);
	loop {
		let pump_net = futures::future::poll_fn(|cx| {
			net.lock().poll(cx);
			Poll::<()>::Pending
		});
		let mut gossip_engine = &mut charlie_gossip_engine;
		futures::select! {
			// pump gossip engine
			_ = gossip_engine => unreachable!(),
			// pump network
			_ = pump_net.fuse() => unreachable!(),
			// verify finality proof has been gossipped
			proof = charlie_gossip_proofs.next() => {
				let proof = proof.unwrap();
				let (round, _) = proof_block_num_and_set_id::<Block>(&proof);
				match round {
					1 => continue, // finality proof generated by Charlie in the previous round
					2 => break,	// finality proof generated by Alice or Bob and gossiped to Charlie
					_ => panic!("Charlie got unexpected finality proof"),
				}
			},
		}
	}
}
