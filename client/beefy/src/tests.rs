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


use crate::{
	aux_schema::{load_persistent, tests::verify_persisted_version},
	beefy_block_import_and_links,
	communication::request_response::{
		on_demand_justifications_protocol_config, BeefyJustifsRequestHandler,
	},
	gossip_protocol_name,
	justification::*,
	keystore::tests::{Keyring, GenericKeyring, SimpleKeyPair, ECDSAnBLSPair},
	keystore::{BeefyECDSAKeystore, BeefyBLSnECDSAKeystore},
	load_or_init_voter_state, wait_for_runtime_pallet, BeefyRPCLinks, BeefyVoterLinks, KnownPeers,
	PersistedState,
};
use beefy_primitives::{
    ecdsa_crypto::{AuthorityId as ECDSAAuthorityId, Public as ECDSAPublic, Signature as ECDSASignature, Pair as ECDSAKeyPair},
    bls_crypto::{AuthorityId as BLSAuthorityId, Public as BLSPublic, Signature as BLSSignature},
	known_payloads,
	mmr::MmrRootProvider,
	BeefyApi, Commitment, ConsensusLog, MmrRootHash, Payload, SignedCommitment, ValidatorSet,
	VersionedFinalityProof, BEEFY_ENGINE_ID,
};
use futures::{future, stream::FuturesUnordered, Future, StreamExt};
use parking_lot::Mutex;
use sc_client_api::{Backend as BackendT, BlockchainEvents, FinalityNotifications, HeaderBackend};
use sc_consensus::{
	BlockImport, BlockImportParams, BoxJustificationImport, ForkChoiceStrategy, ImportResult,
	ImportedAux,
};
use sc_network::{config::RequestResponseConfig, ProtocolName};
use sc_keystore::LocalKeystore;
use sc_network_test::{
	Block, BlockImportAdapter, FullPeerConfig, PassThroughVerifier, Peer, PeersClient,
	PeersFullClient, TestNetFactory,
};
use sc_utils::notification::NotificationReceiver;
use serde::{Deserialize, Serialize};
use sp_api::{ApiRef, ProvideRuntimeApi};
use sp_consensus::BlockOrigin;
use sp_core::H256;
use sp_keystore::{SyncCryptoStorePtr};
use sp_mmr_primitives::{EncodableOpaqueLeaf, Error as MmrError, MmrApi, Proof};
use sp_runtime::{
    codec::{Encode, Decode},
	generic::BlockId,
	traits::{Header as HeaderT, NumberFor},
	BuildStorage, DigestItem, Justifications, Storage,
};
use core::fmt::Debug;
use std::{collections::HashMap, marker::PhantomData, sync::Arc, task::Poll};
use substrate_test_runtime_client::{runtime::Header, ClientExt};
use tokio::time::Duration;

use smart_default::SmartDefault;

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
#[derive(SmartDefault)]
pub(crate) struct PeerData<TSignature> where
	TSignature: Encode + Decode + Debug + Clone + Sync + Send,
{
	pub(crate) beefy_rpc_links: Mutex<Option<BeefyRPCLinks<Block, TSignature>>>,
	pub(crate) beefy_voter_links: Mutex<Option<BeefyVoterLinks<Block, TSignature>>>,
	pub(crate) beefy_justif_req_handler:
		Mutex<Option<BeefyJustifsRequestHandler<Block, PeersFullClient>>>,
}

// #[derive(Default)] can not derive due to generic
#[derive(SmartDefault)]
pub(crate) struct BeefyTestNet<AuthId, TSignature, TBeefyKeystore> where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>,
{
	peers: Vec<BeefyPeer<AuthId, TSignature, TBeefyKeystore>>,
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

	/// Builds the blocks and returns the vector of built block hashes.
	/// Returned vector contains the genesis hash which allows for easy indexing (block number is
	/// equal to index)
	pub(crate) async fn generate_blocks_and_sync(
		&mut self,
		count: usize,
		session_length: u64,
		validator_set: &BeefyValidatorSet<AuthId>,
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
		    beefy_justif_req_handler: Mutex::new(None),
			//..Default::default()
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
					fn mmr_root() -> Result<MmrRootHash, MmrError> {
						Ok($mmr_root)
					}

					fn generate_proof(
						_block_numbers: Vec<u64>,
						_best_known_block_number: Option<u64>
					) -> Result<(Vec<EncodableOpaqueLeaf>, Proof<MmrRootHash>), MmrError> {
						unimplemented!()
					}

					fn verify_proof(_leaves: Vec<EncodableOpaqueLeaf>, _proof: Proof<MmrRootHash>) -> Result<(), MmrError> {
						unimplemented!()
					}

					fn verify_proof_stateless(
						_root: MmrRootHash,
						_leaves: Vec<EncodableOpaqueLeaf>,
						_proof: Proof<MmrRootHash>
					) -> Result<(), MmrError> {
						unimplemented!()
					}
				}
			}
		}
	};
}

create_test_api!(two_validators,  mmr_root: GOOD_MMR_ROOT, Keyring::Alice, Keyring::Bob);
create_test_api!(
    four_validators,
	mmr_root: GOOD_MMR_ROOT,
	Keyring::Alice,
	Keyring::Bob,
	Keyring::Charlie,
	Keyring::Dave
);
create_test_api!(
    bad_four_validators,
    mmr_root: BAD_MMR_ROOT,
    Keyring::Alice,
    Keyring::Bob,
    Keyring::Charlie,
    Keyring::Dave
);

fn add_mmr_digest(header: &mut Header, mmr_hash: MmrRootHash) {
	header.digest_mut().push(DigestItem::Consensus(
		BEEFY_ENGINE_ID,
		ConsensusLog::<ECDSAAuthorityId>::MmrRoot(mmr_hash).encode(),
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

impl BeefyAuthIdMaker for ECDSAAuthorityId 
{
     fn make_beefy_ids(keys: &[Keyring]) -> Vec<Self> {
	     keys.iter().map(|&key| <Keyring as GenericKeyring<ECDSAKeyPair>>::public(key).into()).collect()
	     
    }
}

impl BeefyAuthIdMaker for (ECDSAAuthorityId, BLSAuthorityId)
{
     fn make_beefy_ids(keys: &[Keyring]) -> Vec<Self> {
	     keys.iter().map(|&key| <Keyring as GenericKeyring<ECDSAnBLSPair>>::public(key).into()).collect()
	     
    }
}

pub(crate) fn create_beefy_keystore<TKeyPair: SimpleKeyPair>(authority: Keyring) -> SyncCryptoStorePtr {    
	let keystore = Arc::new(LocalKeystore::in_memory());    
    TKeyPair::generate_in_store(keystore.clone(), authority);
	keystore
}

fn voter_init_setup<AuthId, TSignature, TBeefyKeystore> (
	net: &mut BeefyTestNet<AuthId, TSignature, TBeefyKeystore>,
	finality: &mut futures::stream::Fuse<FinalityNotifications<Block>>,
) -> sp_blockchain::Result<PersistedState<Block, AuthId, TSignature>>
    where
    AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>+ 'static,
{
	let backend = net.peer(0).client().as_backend();
	let api = Arc::new(crate::tests::two_validators::TestApi {});
	let known_peers = Arc::new(Mutex::new(KnownPeers::new()));
	let gossip_validator =
		Arc::new(crate::communication::gossip::GossipValidator::<Block, AuthId, TSignature, TBeefyKeystore>::new(known_peers));
	let mut gossip_engine = sc_network_gossip::GossipEngine::new(
		net.peer(0).network_service().clone(),
		"/beefy/whatever",
		gossip_validator,
		None,
	);
	let best_grandpa =
		futures::executor::block_on(wait_for_runtime_pallet::<_,_, AuthId>(&*api, &mut gossip_engine, finality))
			.unwrap();
	load_or_init_voter_state(&*backend, &*api, best_grandpa, 1)
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
    TSignature: Encode + Decode + Debug + Clone + Sync + Send +  'static,
    TKeyPair: Sync + Send + SimpleKeyPair,
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

async fn run_until<AuthId, TSignature, BKS>(future: impl Future + Unpin, net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>) where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,


{
	let drive_to_completion = futures::future::poll_fn(|cx| {
		net.lock().poll(cx);
		Poll::<()>::Pending
	});
	let _ = future::select(future, drive_to_completion).await;
}

async fn run_for<AuthId, TSignature, BKS>(duration: Duration, net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>) where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,

{
	run_until(Box::pin(tokio::time::sleep(duration)), net).await;
}

pub(crate) fn get_beefy_streams<AuthId, TSignature, BKS>(
	net: &mut BeefyTestNet<AuthId, TSignature, BKS>,
	// peer index and key
	peers: impl Iterator<Item = (usize, Keyring)>,
) -> (Vec<NotificationReceiver<H256>>, Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block, TSignature>>>)
where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
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

async fn wait_for_best_beefy_blocks<AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<H256>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	expected_beefy_blocks: &[u64],
) where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
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

async fn wait_for_beefy_signed_commitments<AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<BeefyVersionedFinalityProof<Block, TSignature>>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	expected_commitment_block_nums: &[u64],
) where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
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
	run_until(wait_for, net).await;
}

async fn streams_empty_after_timeout<T, AuthId, TSignature, BKS>(
	streams: Vec<NotificationReceiver<T>>,
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	timeout: Option<Duration>,
) where
    T: std::fmt::Debug,
    T: std::cmp::PartialEq,
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	if let Some(timeout) = timeout {
		run_for(timeout, net).await;
	}
	for mut stream in streams.into_iter() {
		future::poll_fn(move |cx| {
			assert_eq!(stream.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}
}

async fn finalize_block_and_wait_for_beefy<AuthId, TSignature, BKS>(
	net: &Arc<Mutex<BeefyTestNet<AuthId, TSignature, BKS>>>,
	// peer index and key
	peers: impl Iterator<Item = (usize, Keyring)> + Clone,
	finalize_targets: &[H256],
	expected_beefy: &[u64],
) where
    AuthId: Encode + Decode + Debug + Clone + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
    TSignature: Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq + 'static,
    BKS: BeefyKeystore<AuthId, TSignature, Public = AuthId> + 'static,
{
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());

	for block in finalize_targets {
		peers.clone().for_each(|(index, _)| {
			let client = net.lock().peer(index).client().as_client();
			client.finalize_block(*block, None).unwrap();
		})
	}

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

async fn beefy_finalizing_blocks<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,      
{
 	sp_tracing::try_init_simple();

 	let peers = [Keyring::Alice, Keyring::Bob];
 	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&peers), 0).unwrap();
 	let session_len = 10;
 	let min_block_delta = 4;

 	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(2);

	let api = Arc::new(two_validators::TestApi {});
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy::<two_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, beefy_peers, min_block_delta));

	// push 42 blocks including `AuthorityChange` digests every 10 blocks.
	let hashes = net.generate_blocks_and_sync(42, session_len, &validator_set, true).await;

	let net = Arc::new(Mutex::new(net));

	// Minimum BEEFY block delta is 4.

	let peers = peers.into_iter().enumerate();
	// finalize block #5 -> BEEFY should finalize #1 (mandatory) and #5 from diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &[hashes[1], hashes[5]], &[1, 5]).await;

	// GRANDPA finalize #10 -> BEEFY finalize #10 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &[hashes[10]], &[10]).await;

	// GRANDPA finalize #18 -> BEEFY finalize #14, then #18 (diff-power-of-two rule)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &[hashes[18]], &[14, 18]).await;

	// GRANDPA finalize #20 -> BEEFY finalize #20 (mandatory)
	finalize_block_and_wait_for_beefy(&net, peers.clone(), &[hashes[20]], &[20]).await;

	// GRANDPA finalize #21 -> BEEFY finalize nothing (yet) because min delta is 4
	finalize_block_and_wait_for_beefy(&net, peers, &[hashes[21]], &[]).await;
}

#[tokio::test]
async fn beefy_finalizing_blocks_using_ecdsa_signature() {
    beefy_finalizing_blocks::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn beefy_finalizing_blocks_using_ecdsa_n_bls_signature() {
    beefy_finalizing_blocks::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn lagging_validators<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	sp_tracing::try_init_simple();

	let peers = [Keyring::Alice, Keyring::Bob];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&peers), 0).unwrap();
	let session_len = 30;
	let min_block_delta = 1;

	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(2);
	let api = Arc::new(two_validators::TestApi {});
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy::<two_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, beefy_peers, min_block_delta));

	// push 62 blocks including `AuthorityChange` digests every 30 blocks.
	let hashes = net.generate_blocks_and_sync(62, session_len, &validator_set, true).await;

	let net = Arc::new(Mutex::new(net));

	let peers = peers.into_iter().enumerate();
	// finalize block #15 -> BEEFY should finalize #1 (mandatory) and #9, #13, #14, #15 from
	// diff-power-of-two rule.
	finalize_block_and_wait_for_beefy(
		&net,
		peers.clone(),
		&[hashes[1], hashes[15]],
		&[1, 9, 13, 14, 15],
	)
	.await;

	// Alice finalizes #25, Bob lags behind
	let finalize = hashes[25];
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// Bob catches up and also finalizes #25
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// expected beefy finalizes block #17 from diff-power-of-two
	wait_for_best_beefy_blocks(best_blocks, &net, &[23, 24, 25]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[23, 24, 25]).await;

	// Both finalize #30 (mandatory session) and #32 -> BEEFY finalize #30 (mandatory), #31, #32
	finalize_block_and_wait_for_beefy(
		&net,
		peers.clone(),
		&[hashes[30], hashes[32]],
		&[30, 31, 32],
	)
	.await;

	// Verify that session-boundary votes get buffered by client and only processed once
	// session-boundary block is GRANDPA-finalized (this guarantees authenticity for the new session
	// validator set).

	// Alice finalizes session-boundary mandatory block #60, Bob lags behind
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers.clone());
	let finalize = hashes[60];
	net.lock().peer(0).client().as_client().finalize_block(finalize, None).unwrap();
	// verify nothing gets finalized by BEEFY
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// Bob catches up and also finalizes #60 (and should have buffered Alice's vote on #60)
	let (best_blocks, versioned_finality_proof) = get_beefy_streams(&mut net.lock(), peers);
	net.lock().peer(1).client().as_client().finalize_block(finalize, None).unwrap();
	// verify beefy skips intermediary votes, and successfully finalizes mandatory block #60
	wait_for_best_beefy_blocks(best_blocks, &net, &[60]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[60]).await;
}

#[tokio::test]
async fn lagging_validators_with_ecdsa_crypto() {
    lagging_validators::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn lagging_validators_with_ecdsa_n_bls_crypto() {
    lagging_validators::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn correct_beefy_payload<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	sp_tracing::try_init_simple();

	let peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie, Keyring::Dave];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&peers), 0).unwrap();
	let session_len = 20;
	let min_block_delta = 2;

	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(4);

	// Alice, Bob, Charlie will vote on good payloads
	let good_api = Arc::new(four_validators::TestApi {});
	let good_peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie]
		.iter()
		.enumerate()
		.map(|(id, key)| (id, key, good_api.clone()))
		.collect();
	tokio::spawn(initialize_beefy::<four_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, good_peers, min_block_delta));

	// Dave will vote on bad mmr roots
	let bad_api = Arc::new(bad_four_validators::TestApi {});
	let bad_peers = vec![(3, &Keyring::Dave, bad_api)];
	tokio::spawn(initialize_beefy::<bad_four_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, bad_peers, min_block_delta));

	// push 12 blocks
	let hashes = net.generate_blocks_and_sync(12, session_len, &validator_set, false).await;

	let net = Arc::new(Mutex::new(net));
	let peers = peers.into_iter().enumerate();
	// with 3 good voters and 1 bad one, consensus should happen and best blocks produced.
	finalize_block_and_wait_for_beefy(&net, peers, &[hashes[1], hashes[10]], &[1, 9]).await;

	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), [(0, Keyring::Alice)].into_iter());

	// now 2 good validators and 1 bad one are voting
	let hashof11 = hashes[11];
	net.lock().peer(0).client().as_client().finalize_block(hashof11, None).unwrap();
	net.lock().peer(1).client().as_client().finalize_block(hashof11, None).unwrap();
	net.lock().peer(3).client().as_client().finalize_block(hashof11, None).unwrap();

	// verify consensus is _not_ reached
	let timeout = Some(Duration::from_millis(250));
	streams_empty_after_timeout(best_blocks, &net, timeout).await;
	streams_empty_after_timeout(versioned_finality_proof, &net, None).await;

	// 3rd good validator catches up and votes as well
	let (best_blocks, versioned_finality_proof) =
		get_beefy_streams(&mut net.lock(), [(0, Keyring::Alice)].into_iter());
	net.lock().peer(2).client().as_client().finalize_block(hashof11, None).unwrap();

	// verify consensus is reached
	wait_for_best_beefy_blocks(best_blocks, &net, &[11]).await;
	wait_for_beefy_signed_commitments(versioned_finality_proof, &net, &[11]).await;
}

#[tokio::test]
async fn correct_beefy_payload_with_ecdsa_signature() {
    correct_beefy_payload::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn correct_beefy_payload_with_ecdsa_n_bls_signature() {
    correct_beefy_payload::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn beefy_importing_blocks<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	use futures::{future::poll_fn};
	use sc_block_builder::BlockBuilderProvider;
	use sc_client_api::BlockBackend;

	sp_tracing::try_init_simple();

	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(2);

	let client = net.peer(0).client().clone();
	let (mut block_import, _, peer_data) = net.make_block_import(client.clone());
	let PeerData { beefy_voter_links, .. } = peer_data;
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
	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof1 = block.header.hash();

	// Import without justifications.
	let mut justif_recv = justif_stream.subscribe(100_000);
	assert_eq!(
		block_import
			.import_block(params(block.clone(), None), HashMap::new())
			.await
			.unwrap(),
		ImportResult::Imported(ImportedAux { is_new_best: true, ..Default::default() }),
	);
	assert_eq!(
		block_import.import_block(params(block, None), HashMap::new()).await.unwrap(),
		ImportResult::AlreadyInChain,
	);
	// Verify no BEEFY justifications present:
	{
		// none in backend,
		assert_eq!(
			full_client
				.justifications(hashof1)
				.unwrap()
				.and_then(|j| j.get(BEEFY_ENGINE_ID).cloned()),
			None
		);
		// and none sent to BEEFY worker.
		poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}

	// Import with valid justification.
	let parent_id = BlockId::Number(1);
	let block_num = 2;
	let keys = &[Keyring::Alice, Keyring::Bob];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(keys), 0).unwrap();
	let proof = crate::justification::tests::new_finality_proof::<TKeyPair, AuthId, TSignature>(block_num, &validator_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, TSignature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof2 = block.header.hash();
	let mut justif_recv = justif_stream.subscribe(100_000);
	assert_eq!(
		block_import.import_block(params(block, justif), HashMap::new()).await.unwrap(),
		ImportResult::Imported(ImportedAux {
			bad_justification: false,
			is_new_best: true,
			..Default::default()
		}),
	);
	// Verify BEEFY justification successfully imported:
	{
		// still not in backend (worker is responsible for appending to backend),
		assert_eq!(
			full_client
				.justifications(hashof2)
				.unwrap()
				.and_then(|j| j.get(BEEFY_ENGINE_ID).cloned()),
			None
		);
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

	// Import with invalid justification (incorrect validator set).
	let parent_id = BlockId::Number(2);
	let block_num = 3;
	let keys = &[Keyring::Alice];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(keys), 1).unwrap();
	let proof = crate::justification::tests::new_finality_proof::<TKeyPair, AuthId, TSignature>(block_num, &validator_set, keys);
	let versioned_proof: VersionedFinalityProof<NumberFor<Block>, TSignature> = proof.into();
	let encoded = versioned_proof.encode();
	let justif = Some(Justifications::from((BEEFY_ENGINE_ID, encoded)));

	let builder = full_client.new_block_at(&parent_id, Default::default(), false).unwrap();
	let block = builder.build().unwrap().block;
	let hashof3 = block.header.hash();
	let mut justif_recv = justif_stream.subscribe(100_000);
	assert_eq!(
		block_import.import_block(params(block, justif), HashMap::new()).await.unwrap(),
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
		assert_eq!(
			full_client
				.justifications(hashof3)
				.unwrap()
				.and_then(|j| j.get(BEEFY_ENGINE_ID).cloned()),
			None
		);
		// and none sent to BEEFY worker.
		poll_fn(move |cx| {
			assert_eq!(justif_recv.poll_next_unpin(cx), Poll::Pending);
			Poll::Ready(())
		})
		.await;
	}
}

#[tokio::test]
async fn beefy_importing_blocks_with_ecdsa_signature() {
    beefy_importing_blocks::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn beefy_importing_blocks_with_ecdsa_n_bls_signature() {
    beefy_importing_blocks::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn voter_initialization<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	sp_tracing::try_init_simple();
	// Regression test for voter initialization where finality notifications were dropped
	// after waiting for BEEFY pallet availability.

	let peers = [Keyring::Alice, Keyring::Bob];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&peers), 0).unwrap();
	let session_len = 5;
	// Should vote on all mandatory blocks no matter the `min_block_delta`.
	let min_block_delta = 10;

	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(2);
	let api = Arc::new(two_validators::TestApi {});
	let beefy_peers = peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy::<two_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, beefy_peers, min_block_delta));

	// push 26 blocks
	let hashes = net.generate_blocks_and_sync(26, session_len, &validator_set, false).await;
	let net = Arc::new(Mutex::new(net));

	// Finalize multiple blocks at once to get a burst of finality notifications right from start.
	// Need to finalize at least one block in each session, choose randomly.
	// Expect voters to pick up all of them and BEEFY-finalize the mandatory blocks of each session.
	finalize_block_and_wait_for_beefy(
		&net,
		peers.into_iter().enumerate(),
		&[hashes[1], hashes[6], hashes[10], hashes[17], hashes[24], hashes[26]],
		&[1, 5, 10, 15, 20, 25],
	)
	.await;
}

#[tokio::test]
async fn voter_initialization_with_ecdsa_crypto() {
    voter_initialization::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn voter_initialization_with_ecdsa_n_bls_crypto() {
    voter_initialization::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn on_demand_beefy_justification_sync<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,

{
	sp_tracing::try_init_simple();

	let all_peers =
		[Keyring::Alice, Keyring::Bob, Keyring::Charlie, Keyring::Dave];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(&all_peers), 0).unwrap();
	let session_len = 5;
	let min_block_delta = 5;

	let mut net : BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(4);

	// Alice, Bob, Charlie start first and make progress through voting.
	let api = Arc::new(four_validators::TestApi {});
	let fast_peers = [Keyring::Alice, Keyring::Bob, Keyring::Charlie];
	let voting_peers =
		fast_peers.iter().enumerate().map(|(id, key)| (id, key, api.clone())).collect();
	tokio::spawn(initialize_beefy::<four_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, voting_peers, min_block_delta));

	// Dave will start late and have to catch up using on-demand justification requests (since
	// in this test there is no block import queue to automatically import justifications).
	let dave = vec![(3, &Keyring::Dave, api)];
	// Instantiate but don't run Dave, yet.
	let dave_task = initialize_beefy::<four_validators::TestApi, AuthId, TSignature, TBeefyKeystore, TKeyPair>(&mut net, dave, min_block_delta);
	let dave_index = 3;

	// push 30 blocks
	let hashes = net.generate_blocks_and_sync(30, session_len, &validator_set, false).await;

	let fast_peers = fast_peers.into_iter().enumerate();
	let net = Arc::new(Mutex::new(net));
	// With 3 active voters and one inactive, consensus should happen and blocks BEEFY-finalized.
	// Need to finalize at least one block in each session, choose randomly.
	finalize_block_and_wait_for_beefy(
		&net,
		fast_peers.clone(),
		&[hashes[1], hashes[6], hashes[10], hashes[17], hashes[24]],
		&[1, 5, 10, 15, 20],
	)
	.await;

	// Spawn Dave, they are now way behind voting and can only catch up through on-demand justif
	// sync.
	tokio::spawn(dave_task);
	// give Dave a chance to spawn and init.
	run_for(Duration::from_millis(400), &net).await;

	let (dave_best_blocks, _) =
		get_beefy_streams(&mut net.lock(), [(dave_index, Keyring::Dave)].into_iter());
	let client = net.lock().peer(dave_index).client().as_client();
	client.finalize_block(hashes[1], None).unwrap();
	// Give Dave task some cpu cycles to process the finality notification,
	run_for(Duration::from_millis(100), &net).await;
	// freshly spun up Dave now needs to listen for gossip to figure out the state of their peers.

	// Have the other peers do some gossip so Dave finds out about their progress.
	finalize_block_and_wait_for_beefy(&net, fast_peers, &[hashes[25]], &[25]).await;

	// Now verify Dave successfully finalized #1 (through on-demand justification request).
	wait_for_best_beefy_blocks(dave_best_blocks, &net, &[1]).await;

	// Give Dave all tasks some cpu cycles to burn through their events queues,
	run_for(Duration::from_millis(100), &net).await;
	// then verify Dave catches up through on-demand justification requests.
	finalize_block_and_wait_for_beefy(
		&net,
		[(dave_index, Keyring::Dave)].into_iter(),
		&[hashes[6], hashes[10], hashes[17], hashes[24], hashes[26]],
		&[5, 10, 15, 20, 25],
	)
	.await;

	let all_peers = all_peers.into_iter().enumerate();
	// Now that Dave has caught up, sanity check voting works for all of them.
	finalize_block_and_wait_for_beefy(&net, all_peers, &[hashes[30]], &[30]).await;
}

#[tokio::test]
async fn on_demand_beefy_justification_sync_with_ecdsa_signature() {
    on_demand_beefy_justification_sync::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn on_demand_beefy_justification_sync_with_ecdsa_n_bls_signature() {
    on_demand_beefy_justification_sync::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}


async fn  should_initialize_voter_at_genesis<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
 {
	let keys = &[Keyring::Alice];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(keys), 0).unwrap();
	let mut net: BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(1);
	let backend = net.peer(0).client().as_backend();

	// push 15 blocks with `AuthorityChange` digests every 10 blocks
	let hashes = net.generate_blocks_and_sync(15, 10, &validator_set, false).await;

	let mut finality = net.peer(0).client().as_client().finality_notification_stream().fuse();

	// finalize 13 without justifications
	net.peer(0).client().as_client().finalize_block(hashes[13], None).unwrap();

	// load persistent state - nothing in DB, should init at session boundary
	let persisted_state = voter_init_setup(&mut net, &mut finality).unwrap();

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
	assert_eq!(persisted_state.best_grandpa_block(), 13);
	assert_eq!(
		persisted_state
			.voting_oracle()
			.voting_target(persisted_state.best_beefy_block(), 13),
		Some(1)
	);

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn should_initialize_voter_at_genesis_with_ecdsa_signature() {
    should_initialize_voter_at_genesis::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn should_initialize_voter_at_genesis_with_ecdsa_n_bls_signature() {
    should_initialize_voter_at_genesis::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn should_initialize_voter_when_last_final_is_session_boundary<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	let keys = &[Keyring::Alice];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(keys), 0).unwrap();
	let mut net: BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(1);
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
	let justif = VersionedFinalityProof::<_, TSignature>::V1(SignedCommitment {
		commitment,
		signatures: vec![None],
	});
	backend
		.append_justification(hashes[10], (BEEFY_ENGINE_ID, justif.encode()))
		.unwrap();

	// Test corner-case where session boundary == last beefy finalized,
	// expect rounds initialized at last beefy finalized 10.

	// load persistent state - nothing in DB, should init at session boundary
	let persisted_state = voter_init_setup(&mut net, &mut finality).unwrap();

	// verify voter initialized with single session starting at block 10
	assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), 10);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify block 10 is correctly marked as finalized
	assert_eq!(persisted_state.best_beefy_block(), 10);
	assert_eq!(persisted_state.best_grandpa_block(), 13);
	// verify next vote target is diff-power-of-two block 12
	assert_eq!(
		persisted_state
			.voting_oracle()
			.voting_target(persisted_state.best_beefy_block(), 13),
		Some(12)
	);

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}

#[tokio::test]
async fn should_initialize_voter_when_last_final_is_session_boundary_with_ecdsa_signature() {
    should_initialize_voter_when_last_final_is_session_boundary::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn should_initialize_voter_when_last_final_is_session_boundary_with_ecdsa_n_bls_signature() {
    should_initialize_voter_when_last_final_is_session_boundary::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

async fn should_initialize_voter_at_latest_finalized<TKeyPair, AuthId, TSignature, TBeefyKeystore>()
where TKeyPair : SimpleKeyPair + SimpleKeyPair<Public = AuthId, Signature = TSignature> + 'static,
      TBeefyKeystore: BeefyKeystore<AuthId, TSignature, Public = AuthId>  + 'static,
      AuthId: Clone + Encode + Decode + Debug + Ord + Sync + Send + BeefyAuthIdMaker + std::hash::Hash + 'static,
      TSignature:  Encode + Decode + Debug + Clone + Sync + Send + std::cmp::PartialEq  + 'static,
{
	let keys = &[Keyring::Alice];
	let validator_set = ValidatorSet::new(<AuthId as BeefyAuthIdMaker>::make_beefy_ids(keys), 0).unwrap();
	let mut net: BeefyTestNet<AuthId, TSignature, TBeefyKeystore> = BeefyTestNet::new(1);
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
	let justif = VersionedFinalityProof::<_, TSignature>::V1(SignedCommitment {
		commitment,
		signatures: vec![None],
	});
	backend
		.append_justification(hashes[12], (BEEFY_ENGINE_ID, justif.encode()))
		.unwrap();

	// Test initialization at last BEEFY finalized.

	// load persistent state - nothing in DB, should init at last BEEFY finalized
	let persisted_state = voter_init_setup(&mut net, &mut finality).unwrap();

	// verify voter initialized with single session starting at block 12
	assert_eq!(persisted_state.voting_oracle().sessions().len(), 1);
	let rounds = persisted_state.active_round().unwrap();
	assert_eq!(rounds.session_start(), 12);
	assert_eq!(rounds.validator_set_id(), validator_set.id());

	// verify next vote target is 13
	assert_eq!(persisted_state.best_beefy_block(), 12);
	assert_eq!(persisted_state.best_grandpa_block(), 13);
	assert_eq!(
		persisted_state
			.voting_oracle()
			.voting_target(persisted_state.best_beefy_block(), 13),
		Some(13)
	);

	// verify state also saved to db
	assert!(verify_persisted_version(&*backend));
	let state = load_persistent(&*backend).unwrap().unwrap();
	assert_eq!(state, persisted_state);
}


#[tokio::test]
async fn should_initialize_voter_at_latest_finalized_with_ecdsa_signature() {
    should_initialize_voter_at_latest_finalized::<ECDSAKeyPair, ECDSAPublic, ECDSASignature, BeefyECDSAKeystore>().await;
}

#[tokio::test]
async fn should_initialize_voter_at_latest_finalized_with_ecdsa_n_bls_signature() {
    should_initialize_voter_at_latest_finalized::<ECDSAnBLSPair, (ECDSAPublic,BLSPublic), (ECDSASignature,BLSSignature), BeefyBLSnECDSAKeystore>().await;
}

