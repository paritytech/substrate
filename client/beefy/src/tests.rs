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
use std::{collections::HashMap, marker::PhantomData, sync::Arc, task::Poll};
use tokio::{runtime::Runtime, time::Duration};

use sc_client_api::HeaderBackend;
use sc_consensus::{
	BlockImport, BlockImportParams, BoxJustificationImport, ForkChoiceStrategy, ImportResult,
	ImportedAux,
};
use sc_keystore::LocalKeystore;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	PeersFullClient, TestNetFactory,
};
use sc_utils::notification::NotificationReceiver;

use beefy_primitives::{
	ecdsa_crypto::{AuthorityId, Signature, self, Pair as ECDSAKeyPair},
	mmr::MmrRootProvider,
	BeefyApi, ConsensusLog, MmrRootHash, ValidatorSet, VersionedFinalityProof, BEEFY_ENGINE_ID,
	KEY_TYPE as BeefyKeyType,
};
use sc_network::{config::RequestResponseConfig, ProtocolName};
use sp_mmr_primitives::{BatchProof, EncodableOpaqueLeaf, Error as MmrError, MmrApi, Proof};

use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_consensus::BlockOrigin;
use sp_core::H256;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	codec::{Encode, Decode},
	generic::BlockId,
	traits::{Header as HeaderT, NumberFor},
	BuildStorage, DigestItem, Justifications, Storage,
};
use core::fmt::Debug;

use substrate_test_runtime_client::{runtime::Header, ClientExt};

use crate::{
	beefy_block_import_and_links,
	communication::request_response::{
		on_demand_justifications_protocol_config, BeefyJustifsRequestHandler,
	},
	gossip_protocol_name,
	justification::*,
	keystore::tests::{Keyring, GenericKeyring, SimpleKeyPair},
	BeefyRPCLinks, BeefyVoterLinks,
	keystore::{BeefyECDSAKeystore, BeefyBLSnECDSAKeystore},
};

const GENESIS_HASH: H256 = H256::zero();
fn beefy_gossip_proto_name() -> ProtocolName {
	gossip_protocol_name(GENESIS_HASH, None)
}

const GOOD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0xbf);
const BAD_MMR_ROOT: MmrRootHash = MmrRootHash::repeat_byte(0x42);

type BeefyBlockImport<AuthId, TSignature, TBeefyKeystore> = crate::BeefyBlockImport<
	Block,
	substrate_test_runtime_client::Backend, 
	two_validators::TestApi,
    BlockImportAdapter<PeersClient, sp_api::TransactionFor<two_validators::TestApi, Block>>,
    AuthId,
    TSignature,
    TBeefyKeystore,
>;

pub(crate) type BeefyValidatorSet<AuthId> = ValidatorSet<AuthId>;
pub(crate) type BeefyPeer<AuthId, TSignature, TBeefyKeystore> = Peer<PeerData<TSignature>, BeefyBlockImport<AuthId, TSignature, TBeefyKeystore>>;

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

//#[derive(Default)] can not derive due to generic
pub(crate) struct PeerData<TSignature> where
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
{
	pub(crate) beefy_rpc_links: Mutex<Option<BeefyRPCLinks<Block, TSignature>>>,
	pub(crate) beefy_voter_links: Mutex<Option<BeefyVoterLinks<Block, TSignature>>>,
	pub(crate) beefy_justif_req_handler:
		Mutex<Option<BeefyJustifsRequestHandler<Block, PeersFullClient>>>,
}

impl<TSignature> Default for PeerData<TSignature> where
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
{
    fn default() -> Self {
        Self {
	    ..Default::default()
        }
    }
}

// #[derive(Default)] can not derive due to generic
pub(crate) struct BeefyTestNet<AuthId, TSignature, TBeefyKeystore> where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
{
	peers: Vec<BeefyPeer<AuthId, TSignature, TBeefyKeystore>>,
}

impl<AuthId, TSignature, TBeefyKeystore> Default for BeefyTestNet<AuthId, TSignature, TBeefyKeystore> where
    AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
{
    fn default() -> Self {
        Self {
            ..Default::default()
        }
    }
}

impl<AuthId, TSignature, TBeefyKeystore> BeefyTestNet<AuthId, TSignature, TBeefyKeystore> where
    AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	pub(crate) fn new(n_authority: usize) -> Self {
		let mut net = BeefyTestNet { peers: Vec::with_capacity(n_authority) };

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

	pub(crate) fn generate_blocks_and_sync(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet<AuthId>,
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

impl<AuthId, TSignature, TBeefyKeystore> TestNetFactory for BeefyTestNet<AuthId, TSignature, TBeefyKeystore> where
    AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>+ 'static,
{
	type Verifier = PassThroughVerifier;
	type BlockImport = BeefyBlockImport<AuthId, TSignature, TBeefyKeystore>;
	type PeerData = PeerData<TSignature>;

	fn make_verifier(&self, _client: PeersClient, _: &PeerData<TSignature>) -> Self::Verifier {
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
		let peer_data = PeerData::<TSignature> {
			beefy_rpc_links: Mutex::new(Some(rpc_links)),
			beefy_voter_links: Mutex::new(Some(voter_links)),
			..Default::default()
		};
		(BlockImportAdapter::new(block_import), None, peer_data)
	}

	fn peer(&mut self, i: usize) -> &mut BeefyPeer<AuthId, TSignature, TBeefyKeystore> {
		&mut self.peers[i]
	}

	fn peers(&self) -> &Vec<BeefyPeer<AuthId, TSignature, TBeefyKeystore>> {
		&self.peers
	}

	fn mut_peers<F: FnOnce(&mut Vec<BeefyPeer<AuthId, TSignature, TBeefyKeystore>>)>(&mut self, closure: F) {
		closure(&mut self.peers);
	}

	fn add_full_peer(&mut self) {
		// `add_authority_peer()` used instead.
		unimplemented!()
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
			    impl<AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker> BeefyApi<Block, AuthId> for RuntimeApi
				where
			    {
					fn validator_set() -> Option<BeefyValidatorSet<AuthId>> {
						BeefyValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&[$($inits),+]), 0)
					}
				}

			    impl MmrApi<Block, MmrRootHash, NumberFor<Block>> for RuntimeApi {
					fn generate_proof(_block_number: u64)
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

					fn generate_batch_proof(_block_numbers: Vec<u64>) -> Result<(Vec<EncodableOpaqueLeaf>, BatchProof<MmrRootHash>), MmrError> {
						unimplemented!()
					}

					fn generate_historical_batch_proof(
						_block_numbers: Vec<u64>,
						_best_known_block_number: u64
					) -> Result<(Vec<EncodableOpaqueLeaf>, BatchProof<MmrRootHash>), MmrError> {
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

create_test_api!(two_validators,  mmr_root: GOOD_MMR_ROOT, Keyring::Alice, Keyring::Bob);
// create_test_api!(
//     four_validators,
//     ECDSAKeyPair,
// 	mmr_root: GOOD_MMR_ROOT,
// 	Keyring::Alice,
// 	Keyring::Bob,
// 	Keyring::Charlie,
// 	Keyring::Dave
// );
// create_test_api!(
//     bad_four_validators,
//     ECDSAKeyPair,
// 	mmr_root: BAD_MMR_ROOT,
// 	Keyring::Alice,
// 	Keyring::Bob,
// 	Keyring::Charlie,
// 	Keyring::Dave
// );

fn add_mmr_digest(header: &mut Header, mmr_hash: MmrRootHash) {
	header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthorityId>::MmrRoot(mmr_hash).encode(),
	));
}

fn add_auth_change_digest<AuthId>(header: &mut Header, new_auth_set: BeefyValidatorSet<AuthId>) where
    AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send,
{
	header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<AuthId>::AuthoritiesChange(new_auth_set).encode(),
	));
}

pub(crate) trait BeefyAuthIdMaker : Clone + Encode + Decode + Debug + Ord + Sync + Send {
    
     fn make_beefy_ids(keys: &[Keyring]) -> Vec<Self>;
}

impl BeefyAuthIdMaker for ecdsa_crypto::AuthorityId 
{
     fn make_beefy_ids(keys: &[Keyring]) -> Vec<Self> {
	 keys.iter().map(|&key| <Keyring as GenericKeyring<ecdsa_crypto::Pair>>::public(key).into()).collect()
	     
    }
}

pub(crate) fn create_beefy_keystore<TKeyPair: SimpleKeyPair>(authority: Keyring) -> SyncCryptoStorePtr {    
	let keystore = Arc::new(LocalKeystore::in_memory());
	SyncCryptoStore::ecdsa_generate_new(&*keystore, BeefyKeyType, Some(&<Keyring as GenericKeyring<TKeyPair>>::to_seed(authority)))
		.expect("Creates authority key");
	keystore
}

use crate::keystore::BeefyKeystore;
// Spawns beefy voters. Returns a future to spawn on the runtime.
fn initialize_beefy<API, AuthId, TSignature, BKS, TKeyPair>(
	net: &mut BeefyTestNet<AuthId, TSignature, BKS>,
	peers: Vec<(usize, &Keyring, Arc<API>)>,
	min_block_delta: u32,
) -> impl Future<Output = ()>
where
	API: ProvideRuntimeApi<Block> + Default + Sync + Send,
    API::Api: BeefyApi<Block, AuthId> + MmrApi<Block, MmrRootHash, NumberFor<Block>>,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + Default + 'static,
    TKeyPair: Debug + Ord + Sync + Send + SimpleKeyPair,
    AuthId: Clone + Encode + Decode + Debug + Ord + BeefyAuthIdMaker + std::hash::Hash + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	let tasks = FuturesUnordered::new();

	for (peer_id, key, api) in peers.into_iter() {
		let peer = &net.peers[peer_id];

		let keystore = create_beefy_keystore::<TKeyPair>(key.clone());

		let (_, _, peer_data) = net.make_block_import(peer.client().clone());
		let PeerData { beefy_rpc_links, beefy_voter_links, .. } = peer_data;

		let beefy_voter_links = beefy_voter_links.lock().take();
		*peer.data.beefy_rpc_links.lock() = beefy_rpc_links.lock().take();
		*peer.data.beefy_voter_links.lock() = beefy_voter_links.clone();

		let on_demand_justif_handler = peer.data.beefy_justif_req_handler.lock().take().unwrap();

		let network_params = crate::BeefyNetworkParams {
			network: peer.network_service().clone(),
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
			key_store: BKS::new(keystore),
			network_params,
			links: beefy_voter_links.unwrap(),
			min_block_delta,
			prometheus_registry: None,
			on_demand_justifications_handler: on_demand_justif_handler,
			_auth_id: PhantomData,
			_signature: PhantomData,

		};
		let task = crate::start_beefy_gadget::<_, _, _, _, _, _, _, _, _>(beefy_params);

		fn assert_send<T: Send>(_: &T) {}
		assert_send(&task);
		tasks.push(task);
	}

	tasks.for_each(|_| async move {})
}

fn block_until<AuthId, TSignature, BKS>(future: impl Future + Unpin, net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>, runtime: &mut Runtime) where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,


{
	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	runtime.block_on(future::select(future, drive_to_completion));
}

fn run_for<AuthId, TSignature, BKS>(duration: Duration, net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>, runtime: &mut Runtime) where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,

{
	let sleep = runtime.spawn(async move { tokio::time::sleep(duration).await });
	block_until(sleep, net, runtime);
}

pub(crate) fn get_beefy_streams<AuthId, TSignature, BKS>(
	net: &mut BeefyTestNet<AuthId, TSignature, BKS>,
	// peer index and key
	peers: impl Iterator<Item = (usize, Keyring)>,
) -> (Vec<NotificationReceiver<H256>>, Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block, TSignature>>>)
where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	let mut best_block_streams = Vec::new();
	let mut versioned_finality_proof_streams = Vec::new();
	peers.for_each(|(index, _)| {
		let beefy_rpc_links = net.peer(index).data.beefy_rpc_links.lock().clone().unwrap();
		let BeefyRPCLinks { from_voter_justif_stream, from_voter_best_beefy_stream } =
			beefy_rpc_links;
		best_block_streams.push(from_voter_best_beefy_stream.subscribe());
		versioned_finality_proof_streams.push(from_voter_justif_stream.subscribe());
	});
	(best_block_streams, versioned_finality_proof_streams)
}

fn wait_for_best_beefy_blocks<AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<H256>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	runtime: &mut Runtime,
	expected_beefy_blocks: &[u64],
) where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
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

fn wait_for_beefy_signed_commitments<AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block, TSignature>>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	runtime: &mut Runtime,
	expected_commitment_block_nums: &[u64],
) where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
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

fn streams_empty_after_timeout<T, AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<T>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	runtime: &mut Runtime,
	timeout: Option<Duration>,
) where
    T: std::fmt::Debug,
    T: std::cmp::PartialEq,
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
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

fn finalize_block_and_wait_for_beefy<AuthId, TSignature, BKS>(
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	// peer index and key
	peers: impl Iterator<Item = (usize, Keyring)> + Clone,
	runtime: &mut Runtime,
	finalize_targets: &[u64],
	expected_beefy: &[u64],
) where
    AuthId: Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());

	for block in finalize_targets {
		let finalize = BlockId::number(*block);
		peers.clone().for_each(|(index, _)| {
			net.lock()
				.peer(index)
				.client()
				.as_client()
				.finalize_block(finalize, None)
				.unwrap();
		})
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

// #[test]
// fn beefy_finalizing_blocks() {
// 	sp_tracing::try_init_simple();

// 	let mut runtime = Runtime::new().unwrap();
// 	let peers = [Keyring::Alice, Keyring::Bob];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
// 	let session_len = 10;
// 	let min_block_delta = 4;

// 	let mut net = BeefyTestNet::new(2);

// 	let api = Arc::new(two_validators::TestApi {});
// 	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
// 	runtime.spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

// 	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
// 	net.generate_blocks_and_sync(42, session_len, &validator_set, true);

// 	let net = Arc::new(Mutex::new(net));

// 	// Minimum BEEFY block delta is 4.

// 	let peers = peers.into_iter().enumerate();
// 	// finalize block #5 -> BEEFY should finalize #1 (mandatory) and #5 from diff-power-of-two rule.
// 	finalize_block_and_wait_for_beefy(&net, peers.clone(), &mut runtime, &[5], &[1, 5]);

// 	// GRANDPA finalize #10 -> BEEFY finalize #10 (mandatory)
// 	finalize_block_and_wait_for_beefy(&net, peers.clone(), &mut runtime, &[10], &[10]);

// 	// GRANDPA finalize #18 -> BEEFY finalize #14, then #18 (diff-power-of-two rule)
// 	finalize_block_and_wait_for_beefy(&net, peers.clone(), &mut runtime, &[18], &[14, 18]);

// 	// GRANDPA finalize #20 -> BEEFY finalize #20 (mandatory)
// 	finalize_block_and_wait_for_beefy(&net, peers.clone(), &mut runtime, &[20], &[20]);

// 	// GRANDPA finalize #21 -> BEEFY finalize nothing (yet) because min delta is 4
// 	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[21], &[]);
// }

// #[test]
// fn lagging_validators() {
// 	sp_tracing::try_init_simple();

// 	let mut runtime = Runtime::new().unwrap();
// 	let peers = [Keyring::Alice, Keyring::Bob];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
// 	let session_len = 30;
// 	let min_block_delta = 1;

// 	let mut net = BeefyTestNet::new(2);
// 	let api = Arc::new(two_validators::TestApi {});
// 	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
// 	runtime.spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

// 	// push 62 blocks including `AuthorityChange` digests every 30 blocks.
// 	net.generate_blocks_and_sync(62, session_len, &validator_set, true);

// 	let net = Arc::new(Mutex::new(net));

// 	let peers = peers.into_iter().enumerate();
// 	// finalize block #15 -> BEEFY should finalize #1 (mandatory) and #9, #13, #14, #15 from
// 	// diff-power-of-two rule.
// 	finalize_block_and_wait_for_beefy(
// 		&net,
// 		peers.clone(),
// 		&mut runtime,
// 		&[15],
// 		&[1, 9, 13, 14, 15],
// 	);

// 	// Alice finalizes #25, Bob lags behind
// 	let finalize = BlockId::number(25);
// 	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
// 	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
// 	// verify nothing gets finalized by BEEFY
// 	let timeout = Some(Duration::from_millis(250));
// 	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
// 	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

// 	// Bob catches up and also finalizes #25
// 	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
// 	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
// 	// expected beefy finalizes block #17 from diff-power-of-two
// 	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[23, 24, 25]);
// 	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[23, 24, 25]);

// 	// Both finalize #30 (mandatory session) and #32 -> BEEFY finalize #30 (mandatory), #31, #32
// 	finalize_block_and_wait_for_beefy(&net, peers.clone(), &mut runtime, &[30, 32], &[30, 31, 32]);

// 	// Verify that session-boundary votes get buffered by client and only processed once
// 	// session-boundary block is GRANDPA-finalized (this guarantees authenticity for the new session
// 	// validator set).

// 	// Alice finalizes session-boundary mandatory block #60, Bob lags behind
// 	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
// 	let finalize = BlockId::number(60);
// 	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
// 	// verify nothing gets finalized by BEEFY
// 	let timeout = Some(Duration::from_millis(250));
// 	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
// 	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

// 	// Bob catches up and also finalizes #60 (and should have buffered Alice's vote on #60)
// 	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
// 	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
// 	// verify beefy skips intermediary votes, and successfully finalizes mandatory block #60
// 	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[60]);
// 	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[60]);
// }

// #[test]
// fn correct_beefy_payload() {
// 	sp_tracing::try_init_simple();

// 	let mut runtime = Runtime::new().unwrap();
// 	let peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie, Keyring::Dave];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
// 	let session_len = 20;
// 	let min_block_delta = 2;

// 	let mut net = BeefyTestNet::new(4);

// 	// Alice, Bob, Charlie will vote on good payloads
// 	let good_api = Arc::new(four_validators::TestApi {});
// 	let good_peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie]
// 		.iter()
// 		.enumerate()
// 		.map(|(id, key)| (id, key, good_api.clone()))
// 		.collect();
// 	runtime.spawn(initialize_beefy(&mut net, good_peers, min_block_delta));

// 	// Dave will vote on bad mmr roots
// 	let bad_api = Arc::new(bad_four_validators::TestApi {});
// 	let bad_peers = vec![(3, &Keyring::Dave, bad_api)];
// 	runtime.spawn(initialize_beefy(&mut net, bad_peers, min_block_delta));

// 	// push 12 blocks
// 	net.generate_blocks_and_sync(12, session_len, &validator_set, false);

// 	let net = Arc::new(Mutex::new(net));
// 	let peers = peers.into_iter().enumerate();
// 	// with 3 good voters and 1 bad one, consensus should happen and best blocks produced.
// 	finalize_block_and_wait_for_beefy(&net, peers, &mut runtime, &[10], &[1, 9]);

// 	let (best_blocks, versioned_finality_proof) =
// 		get_beefy_streams(&mut net.lock(), [(0, Keyring::Alice)].into_iter());

// 	// now 2 good validators and 1 bad one are voting
// 	net.lock()
// 		.peer(0)
// 		.client()
// 		.as_client()
// 		.finalize_block(BlockId::number(11), None)
// 		.unwrap();
// 	net.lock()
// 		.peer(1)
// 		.client()
// 		.as_client()
// 		.finalize_block(BlockId::number(11), None)
// 		.unwrap();
// 	net.lock()
// 		.peer(3)
// 		.client()
// 		.as_client()
// 		.finalize_block(BlockId::number(11), None)
// 		.unwrap();

// 	// verify consensus is _not_ reached
// 	let timeout = Some(Duration::from_millis(250));
// 	streams_empty_after_timeout(best_blocks, &net, &mut runtime, timeout);
// 	streams_empty_after_timeout(versioned_finality_proof, &net, &mut runtime, None);

// 	// 3rd good validator catches up and votes as well
// 	let (best_blocks, versioned_finality_proof) =
// 		get_beefy_streams(&mut net.lock(), [(0, Keyring::Alice)].into_iter());
// 	net.lock()
// 		.peer(2)
// 		.client()
// 		.as_client()
// 		.finalize_block(BlockId::number(11), None)
// 		.unwrap();

// 	// verify consensus is reached
// 	wait_for_best_beefy_blocks(best_blocks, &net, &mut runtime, &[11]);
// 	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &mut runtime, &[11]);
// }

// #[test]
// fn beefy_importing_blocks() {
// 	use futures::{executor::block_on, future::poll_fn, task::Poll};
// 	use sc_block_builder::BlockBuilderProvider;
// 	use sc_client_api::BlockBackend;

// 	sp_tracing::try_init_simple();

// 	let mut net = BeefyTestNet::new(2);

// 	let client = net.peer(0).client().clone();
// 	let (mut block_import, _, peer_data) = net.make_block_import(client.clone());
// 	let PeerData { beefy_voter_links, .. } = peer_data;
// 	let justif_stream = beefy_voter_links.lock().take().unwrap().from_block_import_justif_stream;

// 	let params = |block: Block, justifications: Option<Justifications>| {
// 		let mut import = BlockImportParams::new(BlockOrigin::File, block.header);
// 		import.justifications = justifications;
// 		import.body = Some(block.extrinsics);
// 		import.finalized = true;
// 		import.fork_choice = Some(ForkChoiceStrategy::LongestChain);
// 		import
// 	};

// 	let full_client = client.as_client();
// 	let parent_id = BlockId::Number(0);
// 	let block_id = BlockId::Number(1);
// 	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
// 	let block = builder.build().unwrap().block;

// 	// Import without justifications.
// 	let mut justif_recv = justif_stream.subscribe();
// 	assert_eq!(
// 		block_on(block_import.import_block(params(block.clone(), None), HashMap::new())).unwrap(),
// 		ImportResult::Imported(ImportedAux { is_new_best: true, ..Default::default() }),
// 	);
// 	assert_eq!(
// 		block_on(block_import.import_block(params(block, None), HashMap::new())).unwrap(),
// 		ImportResult::AlreadyInChain
// 	);
// 	// Verify no justifications present:
// 	{
// 		// none in backend,
// 		assert!(full_client.justifications(&block_id).unwrap().is_none());
// 		// and none sent to BEEFY worker.
// 		block_on(poll_fn(move |cx| {
// 			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
// 			Poll::Ready(())
// 		}));
// 	}

// 	// Import with valid justification.
// 	let parent_id = BlockId::Number(1);
// 	let block_num = 2;
// 	let keys = &[Keyring::Alice, Keyring::Bob];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 0).unwrap();
// 	let proof = crate::justification::tests::new_finality_proof(block_num, &validator_set, keys);
// 	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
// 	let encoded = versioned_proof.encode();
// 	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

// 	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
// 	let block = builder.build().unwrap().block;
// 	let mut justif_recv = justif_stream.subscribe();
// 	assert_eq!(
// 		block_on(block_import.import_block(params(block, justif), HashMap::new())).unwrap(),
// 		ImportResult::Imported(ImportedAux {
// 			bad_justification: false,
// 			is_new_best: true,
// 			..Default::default()
// 		}),
// 	);
// 	// Verify justification successfully imported:
// 	{
// 		// available in backend,
// 		assert!(full_client.justifications(&BlockId::Number(block_num)).unwrap().is_some());
// 		// and also sent to BEEFY worker.
// 		block_on(poll_fn(move |cx| {
// 			match justif_recv.poll_next_unpin(cx) {
// 				Poll::Ready(Some(_justification)) => (),
// 				v => panic!("unexpected value: {:?}", v),
// 			}
// 			Poll::Ready(())
// 		}));
// 	}

// 	// Import with invalid justification (incorrect validator set).
// 	let parent_id = BlockId::Number(2);
// 	let block_num = 3;
// 	let keys = &[Keyring::Alice];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(keys), 1).unwrap();
// 	let proof = crate::justification::tests::new_finality_proof(block_num, &validator_set, keys);
// 	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, Signature> = proof.into();
// 	let encoded = versioned_proof.encode();
// 	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

// 	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
// 	let block = builder.build().unwrap().block;
// 	let mut justif_recv = justif_stream.subscribe();
// 	assert_eq!(
// 		block_on(block_import.import_block(params(block, justif), HashMap::new())).unwrap(),
// 		ImportResult::Imported(ImportedAux {
// 			// Still `false` because we don't want to fail import on bad BEEFY justifications.
// 			bad_justification: false,
// 			is_new_best: true,
// 			..Default::default()
// 		}),
// 	);
// 	// Verify bad justifications was not imported:
// 	{
// 		// none in backend,
// 		assert!(full_client.justifications(&block_id).unwrap().is_none());
// 		// and none sent to BEEFY worker.
// 		block_on(poll_fn(move |cx| {
// 			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
// 			Poll::Ready(())
// 		}));
// 	}
// }

// #[test]
// fn voter_initialization() {
// 	sp_tracing::try_init_simple();
// 	// Regression test for voter initialization where finality notifications were dropped
// 	// after waiting for BEEFY pallet availability.

// 	let mut runtime = Runtime::new().unwrap();
// 	let peers = [Keyring::Alice, Keyring::Bob];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(&peers), 0).unwrap();
// 	let session_len = 5;
// 	// Should vote on all mandatory blocks no matter the `min_block_delta`.
// 	let min_block_delta = 10;

// 	let mut net = BeefyTestNet::new(2);
// 	let api = Arc::new(two_validators::TestApi {});
// 	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
// 	runtime.spawn(initialize_beefy(&mut net, beefy_peers, min_block_delta));

// 	// push 26 blocks
// 	net.generate_blocks_and_sync(26, session_len, &validator_set, false);
// 	let net = Arc::new(Mutex::new(net));

// 	// Finalize multiple blocks at once to get a burst of finality notifications right from start.
// 	// Need to finalize at least one block in each session, choose randomly.
// 	// Expect voters to pick up all of them and BEEFY-finalize the mandatory blocks of each session.
// 	finalize_block_and_wait_for_beefy(
// 		&net,
// 		peers.into_iter().enumerate(),
// 		&mut runtime,
// 		&[1, 6, 10, 17, 24, 26],
// 		&[1, 5, 10, 15, 20, 25],
// 	);
// }

// #[test]
// fn on_demand_beefy_justification_sync() {
// 	sp_tracing::try_init_simple();

// 	let mut runtime = Runtime::new().unwrap();
// 	let all_peers =
// 		[Keyring::Alice, Keyring::Bob, Keyring::Charlie, Keyring::Dave];
// 	let validator_set = ValidatorSet::new(make_beefy_ids(&all_peers), 0).unwrap();
// 	let session_len = 5;
// 	let min_block_delta = 5;

// 	let mut net = BeefyTestNet::new(4);

// 	// Alice, Bob, Charlie start first and make progress through voting.
// 	let api = Arc::new(four_validators::TestApi {});
// 	let fast_peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie];
// 	let voting_peers =
// 		fast_peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
// 	runtime.spawn(initialize_beefy(&mut net, voting_peers, min_block_delta));

// 	// Dave will start late and have to catch up using on-demand justification requests (since
// 	// in this test there is no block import queue to automatically import justifications).
// 	let dave = vec![(3, &Keyring::Dave, api)];
// 	// Instantiate but don't run Dave, yet.
// 	let dave_task = initialize_beefy(&mut net, dave, min_block_delta);
// 	let dave_index = 3;

// 	// push 30 blocks
// 	net.generate_blocks_and_sync(30, session_len, &validator_set, false);

// 	let fast_peers = fast_peers.into_iter().enumerate();
// 	let net = Arc::new(Mutex::new(net));
// 	// With 3 active voters and one inactive, consensus should happen and blocks BEEFY-finalized.
// 	// Need to finalize at least one block in each session, choose randomly.
// 	finalize_block_and_wait_for_beefy(
// 		&net,
// 		fast_peers.clone(),
// 		&mut runtime,
// 		&[1, 6, 10, 17, 24],
// 		&[1, 5, 10, 15, 20],
// 	);

// 	// Spawn Dave, he's now way behind voting and can only catch up through on-demand justif sync.
// 	runtime.spawn(dave_task);
// 	// give Dave a chance to spawn and init.
// 	run_for(Duration::from_millis(400), &net, &mut runtime);

// 	let (dave_best_blocks, _) =
// 		get_beefy_streams(&mut net.lock(), [(dave_index, Keyring::Dave)].into_iter());
// 	net.lock()
// 		.peer(dave_index)
// 		.client()
// 		.as_client()
// 		.finalize_block(BlockId::number(1), None)
// 		.unwrap();
// 	// Give Dave task some cpu cycles to process the finality notification,
// 	run_for(Duration::from_millis(100), &net, &mut runtime);
// 	// freshly spun up Dave now needs to listen for gossip to figure out the state of his peers.

// 	// Have the other peers do some gossip so Dave finds out about their progress.
// 	finalize_block_and_wait_for_beefy(&net, fast_peers, &mut runtime, &[25], &[25]);

// 	// Now verify Dave successfully finalized #1 (through on-demand justification request).
// 	wait_for_best_beefy_blocks(dave_best_blocks, &net, &mut runtime, &[1]);

// 	// Give Dave all tasks some cpu cycles to burn through their events queues,
// 	run_for(Duration::from_millis(100), &net, &mut runtime);
// 	// then verify Dave catches up through on-demand justification requests.
// 	finalize_block_and_wait_for_beefy(
// 		&net,
// 		[(dave_index, Keyring::Dave)].into_iter(),
// 		&mut runtime,
// 		&[6, 10, 17, 24, 26],
// 		&[5, 10, 15, 20, 25],
// 	);

// 	let all_peers = all_peers.into_iter().enumerate();
// 	// Now that Dave has caught up, sanity check voting works for all of them.
// 	finalize_block_and_wait_for_beefy(&net, all_peers, &mut runtime, &[30], &[30]);
// }
