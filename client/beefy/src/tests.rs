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
use std::{collections::HashMap, sync::Arc, task::Poll};
use tokio::{runtime::Runtime, time::Duration};

use sc_chain_spec::{ChainSpec, GenericChainSpec};
use sc_client_api::HeaderBackend;
use sc_consensus::{
	BlockImport, BlockImportParams, BoxJustificationImport, ForkChoiceStrategy, ImportResult,
	ImportedAux,
};
use sc_keystore::LocalKeystore;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	TestNetFactory,
};
use sc_utils::notification::NotificationReceiver;

use beefy_primitives::{
	crypto::{AuthorityId, Signature},
	BeefyApi, ConsensusLog, MmrRootHash, ValidatorSet, VersionedFinalityProof, BEEFY_ENGINE_ID,
	KEY_TYPE as BeefyKeyType,
};
use sp_mmr_primitives::{
	BatchProof, EncodableOpaqueLeaf, Error as MmrError, LeafIndex, MmrApi, Proof,
};

use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_consensus::BlockOrigin;
use sp_core::H256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	codec::Encode,
	generic::BlockId,
	traits::{Header as HeaderT, NumberFor},
	BuildStorage, DigestItem, Justifications, Storage,
};

use substrate_test_runtime_client::{runtime::Header, ClientExt};

use crate::{
	beefy_block_import_and_links, beefy_protocol_name, justification::*,
	keystore::tests::Keyring as BeefyKeyring, BeefyRPCLinks, BeefyVoterLinks,
};

pub(crate) const BEEFY_PROTOCOL_NAME: &'static str = "/beefy/1";
const GOOD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0xbf);
const BAD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0x42);

type BeefyBlockImport = crate::BeefyBlockImport<
	Block,
	substrate_test_runtime_client::Backend,
	two_validators::TestApi,
	BlockImportAdapter<PeersClient, sp_api::TransactionFor<two_validators::TestApi, Block>>,
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

#[test]
fn beefy_protocol_name() {
	let chain_spec = GenericChainSpec::<Genesis>::from_json_bytes(
		&include_bytes!("../../chain-spec/res/chain_spec.json")[..],
	)
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

#[derive(Default)]
pub(crate) struct PeerData {
	pub(crate) beefy_rpc_links: Mutex<Option<BeefyRPCLinks<Block>>>,
	pub(crate) beefy_voter_links: Mutex<Option<BeefyVoterLinks<Block>>>,
}

#[derive(Default)]
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

	pub(crate) fn generate_blocks_and_sync(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet,
		include_mmr_digest: bool,
	) {
		self.peer(0).generate_blocks(count, BlockOrigin::File, |builder| {
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
		self.block_until_sync();
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
		let inner = BlockImportAdapter::new(client.clone());
		let (block_import, voter_links, rpc_links) = beefy_block_import_and_links(
			inner,
			client.as_backend(),
			Arc::new(two_validators::TestApi {}),
		);
		let peer_data = PeerData {
			beefy_rpc_links: Mutex::new(Some(rpc_links)),
			beefy_voter_links: Mutex::new(Some(voter_links)),
		};
		(BlockImportAdapter::new(block_import), None, peer_data)
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

macro_rules! create_test_api {
    ( $api_name:ident, mmr_root: $mmr_root:expr, $($inits:expr),+ ) => {
		pub(crate) mod $api_name {
			use super::*;

			#[derive(Clone, Default)]
			pub(crate) struct TestApi {}

			// compiler gets confused and warns us about unused inner
			#[allow(dead_code)]
			pub(crate) struct RuntimeApi {
				inner: TestApi,
			}

			impl ProvideRuntimeApi<Block> for TestApi {
				type Api = RuntimeApi;
				fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api> {
					RuntimeApi { inner: self.clone() }.into()
				}
			}
			sp_api::mock_impl_runtime_apis! {
				impl BeefyApi<Block> for RuntimeApi {
					fn validator_set() -> Option<BeefyValidatorSet> {
						BeefyValidatorSet::new(make_beefy_ids(&[$($inits),+]), 0)
					}
				}

				impl MmrApi<Block, MmrRootHash> for RuntimeApi {
					fn generate_proof(_leaf_index: LeafIndex)
						-> Result<(EncodableOpaqueLeaf, Proof<MmrRootHash>), MmrError> {
						unimplemented!()
					}

					fn verify_proof(_leaf: EncodableOpaqueLeaf, _proof: Proof<MmrRootHash>)
						-> Result<(), MmrError> {
						unimplemented!()
					}

					fn verify_proof_stateless(
						_root: MmrRootHash,
						_leaf: EncodableOpaqueLeaf,
						_proof: Proof<MmrRootHash>
					) -> Result<(), MmrError> {
						unimplemented!()
					}

					fn mmr_root() -> Result<MmrRootHash, MmrError> {
						Ok($mmr_root)
					}

					fn generate_batch_proof(_leaf_indices: Vec<LeafIndex>) -> Result<(Vec<EncodableOpaqueLeaf>, BatchProof<MmrRootHash>), MmrError> {
						unimplemented!()
					}

					fn verify_batch_proof(_leaves: Vec<EncodableOpaqueLeaf>, _proof: BatchProof<MmrRootHash>) -> Result<(), MmrError> {
						unimplemented!()
					}

					fn verify_batch_proof_stateless(
						_root: MmrRootHash,
						_leaves: Vec<EncodableOpaqueLeaf>,
						_proof: BatchProof<MmrRootHash>
					) -> Result<(), MmrError> {
						unimplemented!()
					}
				}
			}
		}
	};
}

create_test_api!(two_validators, mmr_root: GOOD_MMR_ROOT, BeefyKeyring::Alice, BeefyKeyring::Bob);
create_test_api!(
	four_validators,
	mmr_root: GOOD_MMR_ROOT,
	BeefyKeyring::Alice,
	BeefyKeyring::Bob,
	BeefyKeyring::Charlie,
	BeefyKeyring::Dave
);
create_test_api!(
	bad_four_validators,
	mmr_root: BAD_MMR_ROOT,
	BeefyKeyring::Alice,
	BeefyKeyring::Bob,
	BeefyKeyring::Charlie,
	BeefyKeyring::Dave
);

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

pub(crate) fn create_beefy_keystore(authority: BeefyKeyring) -> SyncCryptoStorePtr {
	let keystore = Arc::new(LocalKeystore::in_memory());
	SyncCryptoStore::ecdsa_generate_new(&*keystore, BeefyKeyType, Some(&authority.to_seed()))
		.expect("Creates authority key");
	keystore
}

// Spawns beefy voters. Returns a future to spawn on the runtime.
fn initialize_beefy<API>(
	net: &mut BeefyTestNet,
	peers: Vec<(usize, &BeefyKeyring, Arc<API>)>,
	min_block_delta: u32,
) -> impl Future<Output = ()>
where
	API: ProvideRuntimeApi<Block> + Default + Sync + Send,
	API::Api: BeefyApi<Block> + MmrApi<Block, MmrRootHash>,
{
	let voters = FuturesUnordered::new();

	for (peer_id, key, api) in peers.into_iter() {
		let peer = &net.peers[peer_id];

		let keystore = create_beefy_keystore(*key);

		let (_, _, peer_data) = net.make_block_import(peer.client().clone());
		let PeerData { beefy_rpc_links, beefy_voter_links } = peer_data;

		let beefy_voter_links = beefy_voter_links.lock().take();
		*peer.data.beefy_rpc_links.lock() = beefy_rpc_links.lock().take();
		*peer.data.beefy_voter_links.lock() = beefy_voter_links.clone();

		let beefy_params = crate::BeefyParams {
			client: peer.client().as_client(),
			backend: peer.client().as_backend(),
			runtime: api.clone(),
			key_store: Some(keystore),
			network: peer.network_service().clone(),
			links: beefy_voter_links.unwrap(),
			min_block_delta,
			prometheus_registry: None,
			protocol_name: BEEFY_PROTOCOL_NAME.into(),
		};
		let gadget = crate::start_beefy_gadget::<_, _, _, _, _>(beefy_params);

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
) -> (Vec<NotificationReceiver<H256>>, Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block>>>)
{
	let mut best_block_streams = Vec::new();
	let mut versioned_finality_proof_streams = Vec::new();
	for peer_id in 0..peers.len() {
		let beefy_rpc_links = net.peer(peer_id).data.beefy_rpc_links.lock().clone().unwrap();
		let BeefyRPCLinks { from_voter_justif_stream, from_voter_best_beefy_stream } =
			beefy_rpc_links;
		best_block_streams.push(from_voter_best_beefy_stream.subscribe());
		versioned_finality_proof_streams.push(from_voter_justif_stream.subscribe());
	}
	(best_block_streams, versioned_finality_proof_streams)
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
	streams: Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block>>>,
	net: &Arc<Mutex<BeefyTestNet>>,
	runtime: &mut Runtime,
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
					beefy_primitives::VersionedFinalityProof::V1(sc) => sc,
				};
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
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);

	for block in finalize_targets {
		let finalize = BlockId::number(*block);
		for i in 0..peers.len() {
			net.lock().peer(i).client().as_client().finalize_block(finalize, None).unwrap();
		}
	}

	if expected_beefy.is_empty() {
		// run for quarter second then verify no new best beefy block available
		let timeout = Some(Duration::from_millis(250));
		streams_empty_after_timeout(best_blocks, &net, runtime, timeout);
		streams_empty_after_timeout(versioned_finality_proof, &net, runtime, None);
	} else {
		// run until expected beefy blocks are received
		wait_for_best_beefy_blocks(best_blocks, &net, runtime, expected_beefy);
		wait_for_beefy_signed_commitments(versioned_finality_proof, &net, runtime, expected_beefy);
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

	let api = Arc::new(two_validators::TestApi {});
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	runtime.spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	net.generate_blocks_and_sync(42, session_len, &validator_set, true);

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
	let peers = &[BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(peers), 0).unwrap();
	let session_len = 30;
	let min_block_delta = 1;

	let mut net = BeefyTestNet::new(2, 0);
	let api = Arc::new(two_validators::TestApi {});
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	runtime.spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

	// push 62 blocks including `AuthorityChange` digests every 30 blocks.
	net.generate_blocks_and_sync(62, session_len, &validator_set, true);

	let net = Arc::new(Mutex::new(net));

	// finalize block #15 -> BEEFY should finalize #1 (mandatory) and #9, #13, #14, #15 from
	// diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[15], &[1, 9, 13, 14, 15]);

	// Alice finalizes #25, Bob lags behind
	let finalize = BlockId::number(25);
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

	// Bob catches up and also finalizes #25
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// expected beefy finalizes block #17 from diff-power-of-two
	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[23, 24, 25]);
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[23, 24, 25]);

	// Both finalize #30 (mandatory session) and #32 -> BEEFY finalize #30 (mandatory), #31, #32
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[30, 32], &[30, 31, 32]);

	// Verify that session-boundary votes get buffered by client and only processed once
	// session-boundary block is GRANDPA-finalized (this guarantees authenticity for the new session
	// validator set).

	// Alice finalizes session-boundary mandatory block #60, Bob lags behind
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	let finalize = BlockId::number(60);
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

	// Bob catches up and also finalizes #60 (and should have buffered Alice's vote on #60)
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// verify beefy skips intermediary votes, and successfully finalizes mandatory block #40
	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[60]);
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[60]);
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

	// Alice, Bob, Charlie will vote on good payloads
	let good_api = Arc::new(four_validators::TestApi {});
	let good_peers = [BeefyKeyring::Alice, BeefyKeyring::Bob, BeefyKeyring::Charlie]
		.iter()
		.enumerate()
		.map(|(id, key)| (id, key, good_api.clone()))
		.collect();
	runtime.spawn(initialize_beefy(&mut net, good_peers, min_block_delta));

	// Dave will vote on bad mmr roots
	let bad_api = Arc::new(bad_four_validators::TestApi {});
	let bad_peers = vec![(3, &BeefyKeyring::Dave, bad_api)];
	runtime.spawn(initialize_beefy(&mut net, bad_peers, min_block_delta));

	// push 10 blocks
	net.generate_blocks_and_sync(12, session_len, &validator_set, false);

	let net = Arc::new(Mutex::new(net));
	// with 3 good voters and 1 bad one, consensus should happen and best blocks produced.
	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[10], &[1, 9]);

	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), &[BeefyKeyring::Alice]);

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
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

	// 3rd good validator catches up and votes as well
	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), &[BeefyKeyring::Alice]);
	net.lock()
		.peer(2)
		.client()
		.as_client()
		.finalize_block(BlockId::number(11), None)
		.unwrap();

	// verify consensus is reached
	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[11]);
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[11]);
}

#[test]
fn beefy_importing_blocks() {
	use futures::{executor::block_on, future::poll_fn, task::Poll};
	use sc_block_builder::BlockBuilderProvider;
	use sc_client_api::BlockBackend;

	sp_tracing::try_init_simple();

	let mut net = BeefyTestNet::new(2, 0);

	let client = net.peer(0).client().clone();
	let (mut block_import, _, peer_data) = net.make_block_import(client.clone());
	let PeerData { beefy_rpc_links: _, beefy_voter_links } = peer_data;
	let justif_stream = beefy_voter_links.lock().take().unwrap().from_block_import_justif_stream;

	let params = |block: Block, justifications: Option<Justifications>| {
		let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
		import.justifications = justifications;
		import.body = Some(block.extrinsics);
		import.finalized = true;
		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
		import
	};

	let full_client = client.as_client();
	let parent_id = BlockId::Number(0);
	let block_id = BlockId::Number(1);
	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;

	// Import without justifications.
	let mut justif_recv = justif_stream.subscribe();
	assert_eq!(
		block_on(block_import.import_block(params(block.clone(), None), HashMap::new())).unwrap(),
		ImportResult::Imported(ImportedAux { is_new_best: true, ..Default::default() }),
	);
	assert_eq!(
		block_on(block_import.import_block(params(block, None), HashMap::new())).unwrap(),
		ImportResult::AlreadyInChain
	);
	// Verify no justifications present:
	{
		// none in backend,
		assert!(full_client.justifications(&block_id).unwrap().is_none());
		// and none sent to BEEFY worker.
		block_on(poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		}));
	}

	// Import with valid justification.
	let parent_id = BlockId::Number(1);
	let block_num = 2;
	let keys = &[BeefyKeyring::Alice, BeefyKeyring::Bob];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
	let proof = crate::justification::tests::new_finality_proof(block_num, &validator_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let mut justif_recv = justif_stream.subscribe();
	assert_eq!(
		block_on(block_import.import_block(params(block, justif), HashMap::new())).unwrap(),
		ImportResult::Imported(ImportedAux {
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);
	// Verify justification successfully imported:
	{
		// available in backend,
		assert!(full_client.justifications(&BlockId::Number(block_num)).unwrap().is_some());
		// and also sent to BEEFY worker.
		block_on(poll_fn(move |cx| {
			match justif_recv.poll_next_unpin(cx) {
				Poll::Ready(Some(_justification)) => (),
				v => panic!("unexpected value: {:?}", v),
			}
			Poll::Ready(())
		}));
	}

	// Import with invalid justification (incorrect validator set).
	let parent_id = BlockId::Number(2);
	let block_num = 3;
	let keys = &[BeefyKeyring::Alice];
	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();
	let proof = crate::justification::tests::new_finality_proof(block_num, &validator_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let mut justif_recv = justif_stream.subscribe();
	assert_eq!(
		block_on(block_import.import_block(params(block, justif), HashMap::new())).unwrap(),
		ImportResult::Imported(ImportedAux {
			// Still `false` because we don't want to fail import on bad BEEFY justifications.
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);
	// Verify bad justifications was not imported:
	{
		// none in backend,
		assert!(full_client.justifications(&block_id).unwrap().is_none());
		// and none sent to BEEFY worker.
		block_on(poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		}));
	}
}
