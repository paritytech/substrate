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
use tokio::runtime::Runtime;

use sc_chain_spec::{ChainSpec, GenericChainSpec};
use sc_client_api::HeaderBackend;
use sc_consensus::BoxJustificationImport;
use sc_keystore::LocalKeystore;
use sc_network::config::ProtocolConfig;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	TestNetFactory,
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

use substrate_test_runtime_client::ClientExt;

use crate::{
	beefy_protocol_name, keystore::tests::Keyring as BeefyKeyring, notification::*,
	worker::tests::TestModifiers,
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
pub struct BeefyLinkHalf {
	signed_commitment_stream: BeefySignedCommitmentStream<Block>,
	beefy_best_block_stream: BeefyBestBlockStream<Block>,
}

#[derive(Default)]
struct PeerData {
	beefy_link_half: Mutex<Option<BeefyLinkHalf>>,
}

struct BeefyTestNet {
	peers: Vec<BeefyPeer>,
}

impl BeefyTestNet {
	fn new(n_authority: usize, n_full: usize) -> Self {
		let mut net = BeefyTestNet { peers: Vec::with_capacity(n_authority + n_full) };
		for _ in 0..n_authority {
			net.add_authority_peer();
		}
		for _ in 0..n_full {
			net.add_full_peer();
		}
		net
	}

	fn add_authority_peer(&mut self) {
		self.add_full_peer_with_config(FullPeerConfig {
			notifications_protocols: vec![BEEFY_PROTOCOL_NAME.into()],
			is_authority: true,
			..Default::default()
		})
	}

	fn generate_blocks(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet,
	) {
		self.peer(0).generate_blocks(count, BlockOrigin::File, |builder| {
			let mut block = builder.build().unwrap().block;

			add_mmr_digest(&mut block, MmrRootHash::default());

			if *block.header.number() % session_length == 0 {
				add_auth_change_digest(&mut block, validator_set.clone());
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

fn make_beefy_ids(keys: &[BeefyKeyring]) -> Vec<AuthorityId> {
	keys.iter().map(|key| key.clone().public().into()).collect()
}

fn create_beefy_keystore(authority: BeefyKeyring) -> SyncCryptoStorePtr {
	let keystore = Arc::new(LocalKeystore::in_memory());
	SyncCryptoStore::ecdsa_generate_new(&*keystore, BeefyKeyType, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore
}

// Spawns beefy voters. Returns a future to spawn on the runtime.
fn initialize_beefy(
	net: &mut BeefyTestNet,
	peers: &[BeefyKeyring],
	validators: &ValidatorSet<AuthorityId>,
	min_block_delta: u32,
) -> impl Future<Output = ()> {
	let voters = FuturesUnordered::new();

	for (peer_id, key) in peers.iter().enumerate() {
		let keystore = create_beefy_keystore(*key);

		let (signed_commitment_sender, signed_commitment_stream) =
			BeefySignedCommitmentStream::<Block>::channel();
		let (beefy_best_block_sender, beefy_best_block_stream) =
			BeefyBestBlockStream::<Block>::channel();

		let beefy_link_half = BeefyLinkHalf { signed_commitment_stream, beefy_best_block_stream };
		*net.peers[peer_id].data.beefy_link_half.lock() = Some(beefy_link_half);

		let beefy_params = crate::BeefyParams {
			client: net.peers[peer_id].client().as_client(),
			backend: net.peers[peer_id].client().as_backend(),
			key_store: Some(keystore),
			network: net.peers[peer_id].network_service().clone(),
			signed_commitment_sender,
			beefy_best_block_sender,
			min_block_delta,
			prometheus_registry: None,
			protocol_name: BEEFY_PROTOCOL_NAME.into(),
		};
		let gadget = crate::start_beefy_gadget::<_, _, _, _>(
			beefy_params,
			TestModifiers { active_validators: validators.clone() },
		);

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

fn add_mmr_digest(block: &mut Block, mmr_hash: MmrRootHash) {
	block.header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthorityId>::MmrRoot(mmr_hash).encode(),
	));
}

fn add_auth_change_digest(block: &mut Block, new_auth_set: BeefyValidatorSet) {
	block.header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthorityId>::AuthoritiesChange(new_auth_set).encode(),
	));
}

fn get_best_block_receivers(
	net: &mut BeefyTestNet,
	peers: &[BeefyKeyring],
) -> Vec<NotificationReceiver<H256>> {
	let mut best_block_streams = Vec::new();
	for peer_id in 0..peers.len() {
		let beefy_link_half =
			net.peer(peer_id).data.beefy_link_half.lock().as_ref().unwrap().clone();
		let BeefyLinkHalf { signed_commitment_stream: _, beefy_best_block_stream } =
			beefy_link_half;
		best_block_streams.push(beefy_best_block_stream.subscribe());
	}
	best_block_streams
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

fn finalize_block_and_wait_for_beefy(
	net: &Arc<Mutex<BeefyTestNet>>,
	peers: &[BeefyKeyring],
	runtime: &mut Runtime,
	finalize_target: u32,
	expected_beefy: &[u64],
) {
	let best_block_streams = get_best_block_receivers(&mut *net.lock(), peers);

	let finalize = BlockId::number(finalize_target.into());
	for i in 0..peers.len() {
		net.lock().peer(i).client().as_client().finalize_block(finalize, None).unwrap();
	}
	// TODO: if `expected_beefy.is_empty()` we should _verify_ that `best_block_streams` also empty
	wait_for_best_beefy_blocks(best_block_streams, &net, runtime, expected_beefy);
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
	runtime.spawn(initialize_beefy(&mut net, peers, &validator_set, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	net.generate_blocks(42, session_len, &validator_set);
	net.block_until_sync();

	let net = Arc::new(Mutex::new(net));

	// Minimum BEEFY block delta is 4.

	// finalize block #5 -> BEEFY should finalize #1 (mandatory) and #5 from diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, 5, &[1, 5]);

	// GRANDPA finalize #10 -> BEEFY finalize #10 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, 10, &[10]);

	// GRANDPA finalize #18 -> BEEFY finalize #14, then #18 (diff-power-of-two rule)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, 18, &[14, 18]);

	// GRANDPA finalize #20 -> BEEFY finalize #20 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, 20, &[20]);

	// GRANDPA finalize #21 -> BEEFY finalize nothing (yet)
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, 21, &[]);
}
