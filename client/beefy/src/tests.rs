// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use futures::{future, stream::FuturesUnordered, Future, StreamExt};
use parking_lot::Mutex;
use serde::{Deserialize, Serialize};
use std::{sync::Arc, task::Poll};
use tokio::{runtime::Runtime, time::Duration};

use sc_chain_spec::{ChainSpec, GenericChainSpec};
use sc_client_api::HeaderBackend;
use sc_consensus::BoxJustificationImport;
use sc_keystore::LocalKeystore;
use sc_network::{config::ProtocolConfig, NetworkService};
use sc_network_gossip::GossipEngine;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	PeersFullClient, TestNetFactory,
};
use sc_utils::notification::NotificationReceiver;

use beefy_primitives::{
	crypto::AuthorityId, ConsensusLog, MmrRootHash, ValidatorSet, BEEFY_ENGINE_ID,
	KEY_TYPE as BeefyKeyType,
};
use sp_consensus::BlockOrigin;
use sp_core::H256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	codec::Encode, generic::BlockId, traits::Header as HeaderT, BuildStorage, DigestItem, Storage,
};

use substrate_test_runtime_client::{runtime::Header, Backend, ClientExt};

use crate::{
	beefy_protocol_name,
	keystore::tests::Keyring as BeefyKeyring,
	notification::*,
	worker::{tests::TestModifiers, BeefyWorker},
};

const BEEFY_PROTOCOL_NAME: &'static str = "/beefy/1";

type BeefyValidatorSet = ValidatorSet<AuthorityId>;
type BeefyPeer = Peer<PeerData, PeersClient>;

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

#[test]
fn beefy_protocol_name() {
	let chain_spec = GenericChainSpec::<Genesis>::from_json_file(std::path::PathBuf::from(
		"../chain-spec/res/chain_spec.json",
	))
	.unwrap()
	.cloned_box();

	// Create protocol name using random genesis hash.
	let genesis_hash = H256::random();
	let expected = format!("/{}/beefy/1", hex::encode(genesis_hash));
	let proto_name = beefy_protocol_name::standard_name(&genesis_hash, &chain_spec);
	assert_eq!(proto_name.to_string(), expected);

	// Create protocol name using hardcoded genesis hash. Verify exact representation.
	let genesis_hash = [
		50, 4, 60, 123, 58, 106, 216, 246, 194, 188, 139, 193, 33, 212, 202, 171, 9, 55, 123, 94,
		8, 43, 12, 251, 187, 57, 173, 19, 188, 74, 205, 147,
	];
	let expected =
		"/32043c7b3a6ad8f6c2bc8bc121d4caab09377b5e082b0cfbbb39ad13bc4acd93/beefy/1".to_string();
	let proto_name = beefy_protocol_name::standard_name(&genesis_hash, &chain_spec);
	assert_eq!(proto_name.to_string(), expected);
}

// TODO: compiler warns us about unused `signed_commitment_stream`, will use in later tests
#[allow(dead_code)]
#[derive(Clone)]
pub(crate) struct BeefyLinkHalf {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	beefy_best_block_stream: BeefyBestBlockStream<Block>,
}

#[derive(Default)]
pub(crate) struct PeerData {
	pub(crate) beefy_link_half: Mutex<Option<BeefyLinkHalf>>,
	pub(crate) test_modifiers: Option<TestModifiers>,
}

impl PeerData {
	pub(crate) fn use_validator_set(&mut self, validator_set: &ValidatorSet<AuthorityId>) {
		if let Some(tm) = self.test_modifiers.as_mut() {
			tm.active_validators = validator_set.clone();
		} else {
			self.test_modifiers = Some(TestModifiers {
				active_validators: validator_set.clone(),
				corrupt_mmr_roots: false,
			});
		}
	}
}

pub(crate) struct BeefyTestNet {
	peers: Vec<BeefyPeer>,
}

impl BeefyTestNet {
	pub(crate) fn new(n_authority: usize, n_full: usize) -> Self {
		let mut net = BeefyTestNet { peers: Vec::with_capacity(n_authority + n_full) };
		for _ in 0..n_authority {
			net.add_authority_peer();
		}
		for _ in 0..n_full {
			net.add_full_peer();
		}
		net
	}

	pub(crate) fn add_authority_peer(&mut self) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![BEEFY_PROTOCOL_NAME.into()],
			is_authority: true,
			..Default::default()
		})
	}

	pub(crate) fn generate_blocks(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet,
	) {
		self.peer(0).generate_blocks(count, BlockOrigin::File, |builder| {
			let mut block = builder.build().unwrap().block;

			let block_num = *block.header.number();
			let num_byte = block_num.to_le_bytes().into_iter().next().unwrap();
			let mmr_root = MmrRootHash::repeat_byte(num_byte);

			add_mmr_digest(&mut block.header, mmr_root);

			if block_num % session_length == 0 {
				add_auth_change_digest(&mut block.header, validator_set.clone());
			}

			block
		});
	}
}

impl TestNetFactory for BeefyTestNet {
	type Verifier = PassThroughVerifier;
	type BlockImport = PeersClient;
	type PeerData = PeerData;

	/// Create new test network with peers and given config.
	fn from_config(_config: &ProtocolConfig) -> Self {
		BeefyTestNet { peers: Vec::new() }
	}

	fn make_verifier(
		&self,
		_client: PeersClient,
		_cfg: &ProtocolConfig,
		_: &PeerData,
	) -> Self::Verifier {
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
		(client.as_block_import(), None, PeerData::default())
	}

	fn peer(&mut self, i: usize) -> &mut BeefyPeer {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<BeefyPeer> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<BeefyPeer>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}

	fn add_full_peer(&mut self) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![BEEFY_PROTOCOL_NAME.into()],
			is_authority: false,
			..Default::default()
		})
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
	keys.iter().map(|key| key.clone().public().into()).collect()
}

pub(crate) fn create_beefy_keystore(authority: BeefyKeyring) -> SyncCryptoStorePtr {
	let keystore = Arc::new(LocalKeystore::in_memory());
	SyncCryptoStore::ecdsa_generate_new(&*keystore, BeefyKeyType, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore
}

pub(crate) fn create_beefy_worker(
	peer: &BeefyPeer,
	key: &BeefyKeyring,
	min_block_delta: u32,
) -> BeefyWorker<Block, PeersFullClient, Backend, Arc<NetworkService<Block, H256>>> {
	let keystore = create_beefy_keystore(*key);

	let (signed_commitment_sender, signed_commitment_stream) =
		BeefySignedCommitmentStream::<Block>::channel();
	let (beefy_best_block_sender, beefy_best_block_stream) =
		BeefyBestBlockStream::<Block>::channel();

	let beefy_link_half = BeefyLinkHalf { signed_commitment_stream, beefy_best_block_stream };
	*peer.data.beefy_link_half.lock() = Some(beefy_link_half);
	let test_modifiers = peer.data.test_modifiers.clone().unwrap();

	let network = peer.network_service().clone();
	let sync_oracle = network.clone();
	let gossip_validator = Arc::new(crate::gossip::GossipValidator::new());
	let gossip_engine =
		GossipEngine::new(network, BEEFY_PROTOCOL_NAME, gossip_validator.clone(), None);
	let worker_params = crate::worker::WorkerParams {
		client: peer.client().as_client(),
		backend: peer.client().as_backend(),
		key_store: Some(keystore).into(),
		signed_commitment_sender,
		beefy_best_block_sender,
		gossip_engine,
		gossip_validator,
		min_block_delta,
		metrics: None,
		sync_oracle,
	};

	BeefyWorker::<_, _, _, _>::new(worker_params, test_modifiers)
}

// Spawns beefy voters. Returns a future to spawn on the runtime.
fn initialize_beefy(
	net: &mut BeefyTestNet,
	peers: &[BeefyKeyring],
	min_block_delta: u32,
) -> impl Future<Output = ()> {
	let voters = FuturesUnordered::new();

	for (peer_id, key) in peers.iter().enumerate() {
		let worker = create_beefy_worker(&net.peers[peer_id], key, min_block_delta);
		let gadget = worker.run();

		fn assert_send<T: Send>(_: &T) {}
		assert_send(&gadget);
		voters.push(gadget);
	}

	voters.for_each(|_| async move {})
}

fn block_until(future: impl Future + Unpin, net: &Arc<Mutex<BeefyTestNet>>, runtime: &mut Runtime) {
	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	runtime.block_on(future::select(future, drive_to_completion));
}

fn run_for(duration: Duration, net: &Arc<Mutex<BeefyTestNet>>, runtime: &mut Runtime) {
	let sleep = runtime.spawn(async move { tokio::time::sleep(duration).await });
	block_until(sleep, net, runtime);
}

pub(crate) fn get_beefy_streams(
	net: &mut BeefyTestNet,
	peers: &[BeefyKeyring],
) -> (Vec<NotificationReceiver<H256>>, Vec<NotificationReceiver<BeefySignedCommitment<Block>>>) {
	let mut best_block_streams = Vec::new();
	let mut signed_commitment_streams = Vec::new();
	for peer_id in 0..peers.len() {
		let beefy_link_half =
			net.peer(peer_id).data.beefy_link_half.lock().as_ref().unwrap().clone();
		let BeefyLinkHalf { signed_commitment_stream, beefy_best_block_stream } = beefy_link_half;
		best_block_streams.push(beefy_best_block_stream.subscribe());
		signed_commitment_streams.push(signed_commitment_stream.subscribe());
	}
	(best_block_streams, signed_commitment_streams)
}

fn wait_for_best_beefy_blocks(
	streams: Vec<NotificationReceiver<H256>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	runtime: &mut Runtime,
	expected_beefy_blocks: &[u64],
) {
	let mut wait_for = Vec::new();
	let len = expected_beefy_blocks.len();
	streams.into_iter().enumerate().for_each(|(i, stream)| {
		let mut expected = expected_beefy_blocks.iter();
		wait_for.push(Box::pin(stream.take(len).for_each(move |best_beefy_hash| {
			let expected = expected.next();
			async move {
				let block_id = BlockId::hash(best_beefy_hash);
				let header =
					net.lock().peer(i).client().as_client().expect_header(block_id).unwrap();
				let best_beefy = *header.number();

				assert_eq!(expected, Some(best_beefy).as_ref());
			}
		})));
	});
	let wait_for = futures::future::join_all(wait_for);
	block_until(wait_for, net, runtime);
}

fn wait_for_beefy_signed_commitments(
	streams: Vec<NotificationReceiver<BeefySignedCommitment<Block>>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	runtime: &mut Runtime,
	expected_commitment_block_nums: &[u64],
) {
	let mut wait_for = Vec::new();
	let len = expected_commitment_block_nums.len();
	streams.into_iter().for_each(|stream| {
		let mut expected = expected_commitment_block_nums.iter();
		wait_for.push(Box::pin(stream.take(len).for_each(move |signed_commitment| {
			let expected = expected.next();
			async move {
				let commitment_block_num = signed_commitment.commitment.block_number;
				assert_eq!(expected, Some(commitment_block_num).as_ref());
				// TODO: also verify commitment payload, validator set id, and signatures.
			}
		})));
	});
	let wait_for = futures::future::join_all(wait_for);
	block_until(wait_for, net, runtime);
}

fn streams_empty_after_timeout<T>(
	streams: Vec<NotificationReceiver<T>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	runtime: &mut Runtime,
	timeout: Option<Duration>,
) where
	T: std::fmt::Debug,
	T: std::cmp::PartialEq,
{
	if let Some(timeout) = timeout {
		run_for(timeout, net, runtime);
	}
	streams.into_iter().for_each(|mut stream| {
		runtime.block_on(future::poll_fn(move |cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		}));
	});
}

fn finalize_block_and_wait_for_beefy(
	net: &Arc<Mutex<BeefyTestNet>>,
	peers: &[BeefyKeyring],
	runtime: &mut Runtime,
	finalize_targets: &[u64],
	expected_beefy: &[u64],
) {
	let (best_blocks, signed_commitments) = get_beefy_streams(&mut *net.lock(), peers);

	for block in finalize_targets {
		let finalize = BlockId::number(*block);
		for i in 0..peers.len() {
			net.lock().peer(i).client().as_client().finalize_block(finalize, None).unwrap();
		}
	}

	if expected_beefy.is_empty() {
		// run for 1 second then verify no new best beefy block available
		let timeout = Some(Duration::from_millis(500));
		streams_empty_after_timeout(best_blocks, &net, runtime, timeout);
		streams_empty_after_timeout(signed_commitments, &net, runtime, None);
	} else {
		// run until expected beefy blocks are received
		wait_for_best_beefy_blocks(best_blocks, &net, runtime, expected_beefy);
		wait_for_beefy_signed_commitments(signed_commitments, &net, runtime, expected_beefy);
	}
}

#[test]
fn beefy_finalizing_blocks() {
	sp_tracing::try_init_simple();

	let mut runtime = Runtime::new().unwrap();
	let peers = &[BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(peers), 0).unwrap();
	let session_len = 10;
	let min_block_delta = 4;

	let mut net = BeefyTestNet::new(2, 0);

	for i in 0..peers.len() {
		net.peer(i).data.use_validator_set(&validator_set);
	}
	runtime.spawn(initialize_beefy(&mut net, peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	net.generate_blocks(42, session_len, &validator_set);
	net.block_until_sync();

	let net = Arc::new(Mutex::new(net));

	// Minimum BEEFY block delta is 4.

	// finalize block #5 -> BEEFY should finalize #1 (mandatory) and #5 from diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[5], &[1, 5]);

	// GRANDPA finalize #10 -> BEEFY finalize #10 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[10], &[10]);

	// GRANDPA finalize #18 -> BEEFY finalize #14, then #18 (diff-power-of-two rule)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[18], &[14, 18]);

	// GRANDPA finalize #20 -> BEEFY finalize #20 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[20], &[20]);

	// GRANDPA finalize #21 -> BEEFY finalize nothing (yet) because min delta is 4
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[21], &[]);
}

#[test]
fn lagging_validators() {
	sp_tracing::try_init_simple();

	let mut runtime = Runtime::new().unwrap();
	let peers = &[BeefyKeyring::Charlie, BeefyKeyring::Dave];
	let validator_set = ValidatorSet::new(make_beefy_ids(peers), 0).unwrap();
	let session_len = 30;
	let min_block_delta = 1;

	let mut net = BeefyTestNet::new(2, 0);
	for i in 0..peers.len() {
		net.peer(i).data.use_validator_set(&validator_set);
	}
	runtime.spawn(initialize_beefy(&mut net, peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 30 blocks.
	net.generate_blocks(42, session_len, &validator_set);
	net.block_until_sync();

	let net = Arc::new(Mutex::new(net));

	// finalize block #15 -> BEEFY should finalize #1 (mandatory) and #9, #13, #14, #15 from
	// diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[15], &[1, 9, 13, 14, 15]);

	// Charlie finalizes #25, Dave lags behind
	let finalize = BlockId::number(25);
	let (best_blocks, signed_commitments) = get_beefy_streams(&mut *net.lock(), peers);
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(500));
	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
	streams_empty_after_timeout(signed_commitments, &net, &mut runtime, None);

	// Dave catches up and also finalizes #25
	let (best_blocks, signed_commitments) = get_beefy_streams(&mut *net.lock(), peers);
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// expected beefy finalizes block #17 from diff-power-of-two
	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[23, 24, 25]);
	wait_for_beefy_signed_commitments(signed_commitments, &net, &mut runtime, &[23, 24, 25]);

	// Both finalize #30 (mandatory session) and #32 -> BEEFY finalize #30 (mandatory), #31, #32
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[30, 32], &[30, 31, 32]);
}

#[test]
fn correct_beefy_payload() {
	sp_tracing::try_init_simple();

	let mut runtime = Runtime::new().unwrap();
	let peers =
		&[BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie, BeefyKeyring::Dave];
	let validator_set = ValidatorSet::new(make_beefy_ids(peers), 0).unwrap();
	let session_len = 20;
	let min_block_delta = 2;

	let mut net = BeefyTestNet::new(4, 0);
	for i in 0..peers.len() {
		net.peer(i).data.use_validator_set(&validator_set);
	}

	// Dave will vote on bad mmr roots
	net.peer(3).data.test_modifiers.as_mut().map(|tm| tm.corrupt_mmr_roots = true);
	runtime.spawn(initialize_beefy(&mut net, peers, min_block_delta));

	// push 10 blocks
	net.generate_blocks(12, session_len, &validator_set);
	net.block_until_sync();

	let net = Arc::new(Mutex::new(net));
	// with 3 good voters and 1 bad one, consensus should happen and best blocks produced.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[10], &[1, 9]);

	let (best_blocks, signed_commitments) =
		get_beefy_streams(&mut *net.lock(), &[BeefyKeyring::Alice]);

	// now 2 good validators and 1 bad one are voting
	net.lock()
		.peer(0)
		.client()
		.as_client()
		.finalize_block(BlockId::number(11), None)
		.unwrap();
	net.lock()
		.peer(1)
		.client()
		.as_client()
		.finalize_block(BlockId::number(11), None)
		.unwrap();
	net.lock()
		.peer(3)
		.client()
		.as_client()
		.finalize_block(BlockId::number(11), None)
		.unwrap();

	// verify consensus is _not_ reached
	let timeout = Some(Duration::from_millis(500));
	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
	streams_empty_after_timeout(signed_commitments, &net, &mut runtime, None);

	// 3rd good validator catches up and votes as well
	let (best_blocks, signed_commitments) =
		get_beefy_streams(&mut *net.lock(), &[BeefyKeyring::Alice]);
	net.lock()
		.peer(2)
		.client()
		.as_client()
		.finalize_block(BlockId::number(11), None)
		.unwrap();

	// verify consensus is reached
	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[11]);
	wait_for_beefy_signed_commitments(signed_commitments, &net, &mut runtime, &[11]);
}
