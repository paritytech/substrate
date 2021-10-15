// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! A consensus proposer for "basic" chains which use the primitive
//! inherent-data.

// FIXME #1021 move this into sp-consensus

use codec::Decode;
use extrinsic_info_runtime_api::runtime_api::ExtrinsicInfoRuntimeApi;
use sp_encrypted_tx::EncryptedTxApi;
use futures::{executor, future, future::Either};
use log::{debug, error, info, trace, warn};
use sc_block_builder::{BlockBuilderApi, BlockBuilderProvider};
use sc_client_api::backend;
use sc_telemetry::{telemetry, CONSENSUS_INFO};
use sp_api::{ApiExt, ProvideRuntimeApi, TransactionOutcome};
use sp_blockchain::{ApplyExtrinsicFailed::Validity, Error::ApplyExtrinsicFailed, HeaderBackend};
use sp_consensus::{evaluation, Proposal, RecordProof};
use sp_core::ExecutionContext;
use sp_inherents::InherentData;
use sp_runtime::{
    AccountId32,
	generic::BlockId,
	traits::{BlakeTwo256, Block as BlockT, DigestFor, Hash as HashT, Header as HeaderT},
};
use sp_transaction_pool::{InPoolTransaction, TransactionPool};
use std::marker::PhantomData;
use std::{sync::Arc, time};
use sc_keystore::KeyStorePtr;
use ecies::{utils::{aes_decrypt, decapsulate}, SecretKey, PublicKey};
use sp_core::crypto::KeyTypeId;

use prometheus_endpoint::Registry as PrometheusRegistry;
use sc_proposer_metrics::MetricsLink as PrometheusMetrics;
use std::cell::RefCell;
use std::rc::Rc;

const INVALID_COLLATOR_ID: &str = "invalid collator id";

/// Proposer factory.
pub struct ProposerFactory<A, B, C> {
	/// The client instance.
	client: Arc<C>,
	/// The transaction pool.
	transaction_pool: Arc<A>,
	/// Prometheus Link,
	metrics: PrometheusMetrics,
	/// keystore for encrypted transactions
	keystore: KeyStorePtr,
	/// phantom member to pin the `Backend` type.
	_phantom: PhantomData<B>,
}

impl<A, B, C> ProposerFactory<A, B, C> {
	pub fn new(
		client: Arc<C>,
		transaction_pool: Arc<A>,
		prometheus: Option<&PrometheusRegistry>,
		keystore: KeyStorePtr,
	) -> Self {
		ProposerFactory {
			client,
			transaction_pool,
			metrics: PrometheusMetrics::new(prometheus),
			keystore,
			_phantom: PhantomData,
		}
	}
}

impl<B, Block, C, A> ProposerFactory<A, B, C>
	where
		A: TransactionPool<Block = Block> + 'static,
		B: backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
			+ Send + Sync + 'static,
		C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
			+ BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	pub fn init_with_now(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
		now: Box<dyn Fn() -> time::Instant + Send + Sync>,
	) -> Proposer<B, Block, C, A> {
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);

		info!("🙌 Starting consensus session on top of parent {:?}", parent_hash);

		let proposer = Proposer {
			client: self.client.clone(),
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			transaction_pool: self.transaction_pool.clone(),
			now,
			metrics: self.metrics.clone(),
			keystore: self.keystore.clone(),
			_phantom: PhantomData,
		};

		proposer
	}
}

impl<A, B, Block, C> sp_consensus::Environment<Block> for
	ProposerFactory<A, B, C>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			Block: BlockT,
			C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
				+ Send + Sync + 'static,
			C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
				+ BlockBuilderApi<Block, Error = sp_blockchain::Error>
				+ ExtrinsicInfoRuntimeApi<Block> + EncryptedTxApi<Block> ,
{
	type CreateProposer = future::Ready<Result<Self::Proposer, Self::Error>>;
	type Proposer = Proposer<B, Block, C, A>;
	type Error = sp_blockchain::Error;

	fn init(
		&mut self,
		parent_header: &<Block as BlockT>::Header,
	) -> Self::CreateProposer {
		future::ready(Ok(self.init_with_now(parent_header, Box::new(time::Instant::now))))
	}
}

/// The proposer logic.
pub struct Proposer<B, Block: BlockT, C, A: TransactionPool> {
	client: Arc<C>,
	parent_hash: <Block as BlockT>::Hash,
	parent_id: BlockId<Block>,
	parent_number: <<Block as BlockT>::Header as HeaderT>::Number,
	transaction_pool: Arc<A>,
	now: Box<dyn Fn() -> time::Instant + Send + Sync>,
	metrics: PrometheusMetrics,
	keystore: KeyStorePtr,
	_phantom: PhantomData<B>,
}

impl<A, B, Block, C> sp_consensus::Proposer<Block> for
	Proposer<B, Block, C, A>
		where
			A: TransactionPool<Block = Block> + 'static,
			B: backend::Backend<Block> + Send + Sync + 'static,
			Block: BlockT,
			C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
				+ Send + Sync + 'static,
			C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
				+ BlockBuilderApi<Block, Error = sp_blockchain::Error>
				+ ExtrinsicInfoRuntimeApi<Block>+ EncryptedTxApi<Block> ,
{
	type Transaction = backend::TransactionFor<B, Block>;
	type Proposal = tokio_executor::blocking::Blocking<
		Result<Proposal<Block, Self::Transaction>, Self::Error>
	>;
	type Error = sp_blockchain::Error;

	fn propose(
		self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		max_duration: time::Duration,
		record_proof: RecordProof,
	) -> Self::Proposal {
		tokio_executor::blocking::run(move || {
			// leave some time for evaluation and block finalization (33%)
			let deadline = (self.now)() + max_duration - max_duration / 3;
			self.propose_with(inherent_data, inherent_digests, deadline, record_proof)
		})
	}
}

impl<A, B, Block, C> Proposer<B, Block, C, A>
	where
		A: TransactionPool<Block = Block> + 'static,
		B: backend::Backend<Block> + Send + Sync + 'static,
		Block: BlockT,
		C: BlockBuilderProvider<B, Block, C> + HeaderBackend<Block> + ProvideRuntimeApi<Block>
			+ Send + Sync + 'static,
		C::Api: ApiExt<Block, StateBackend = backend::StateBackendFor<B, Block>>
			+ BlockBuilderApi<Block, Error = sp_blockchain::Error>
			+ ExtrinsicInfoRuntimeApi<Block>+ EncryptedTxApi<Block> ,
{
    fn get_decryption_key(&self, account_id: &AccountId32) -> sp_blockchain::Result<[u8;32]>{

		let keystore = self.keystore.clone();

        let api = self.client.runtime_api();
		let public_key = api.get_authority_public_key(&self.parent_id, account_id)?
            .ok_or(sp_blockchain::Error::Backend("public key not found".to_owned()))?;
		debug!(target:"basic_authorship","public_key id:  {:?}", public_key);

		let key_pair = keystore.clone().read().key_pair_by_type::<sp_core::ecdsa::Pair>(&public_key, KeyTypeId(*b"xxtx"))
            .map_err(|_| sp_blockchain::Error::Backend("key not found in storage".to_owned()))?;

		let seed: [u8; 32] = key_pair.seed();
		let priv_key: SecretKey = SecretKey::parse_slice(&seed).unwrap();

		let dummy_secret_key: SecretKey = SecretKey::default();
		let pub_key: PublicKey = PublicKey::from_secret_key(&dummy_secret_key);

		decapsulate(&pub_key, &priv_key)
            .map_err(|_| sp_blockchain::Error::Backend(String::from("cannot decapsulate aes key for decryption")))
    }

	fn propose_with(
		self,
		inherent_data: InherentData,
		inherent_digests: DigestFor<Block>,
		deadline: time::Instant,
		record_proof: RecordProof,
	) -> Result<Proposal<Block, backend::TransactionFor<B, Block>>, sp_blockchain::Error> {
		/// If the block is full we will attempt to push at most
		/// this number of transactions before quitting for real.
		/// It allows us to increase block utilization.
		const MAX_SKIPPED_TRANSACTIONS: usize = 8;

        let api = self.client.runtime_api();

		// TODO: solve problem of missing pre_digest in testing framework
		// https://trello.com/c/YPt5RKOj/325-newsolve-problem-of-missing-blockbuilderid-information-in-substrate-tests
		let block_builder_id = sc_consensus_babe::extract_pre_digest::<Block>(&inherent_digests)
			.map(|pre_digest| pre_digest.authority_index())
			.map_err(|e| sp_blockchain::Error::Backend(e.to_string()))?;

		let account_id = api.get_account_id(&self.parent_id, block_builder_id)?
            .ok_or(sp_blockchain::Error::Backend(INVALID_COLLATOR_ID.to_owned()))?;
		debug!(target:"basic_authorship", "account id:  {:?}", account_id); 

		let mut block_builder = self.client.new_block_at(
			&self.parent_id,
			inherent_digests,
			record_proof,
		)?;


		let doubly_encrypted_txs = api.get_double_encrypted_transactions(&self.parent_id, &account_id).unwrap();
		let singly_encrypted_txs = api.get_singly_encrypted_transactions(&self.parent_id, &account_id).unwrap();

		debug!(target:"basic_authorship", "found {} double encrypted transactions", doubly_encrypted_txs.len()); 
		debug!(target:"basic_authorship", "found {} singly encrypted transactions", singly_encrypted_txs.len()); 

		let decrypted_inherents = if !singly_encrypted_txs.is_empty() || !doubly_encrypted_txs.is_empty() {
			let aes_key = self.get_decryption_key(&account_id)?;
			debug!(target:"basic_authorship", "aes_key {:?}", aes_key); 
			let decrypted_inherents = singly_encrypted_txs.into_iter().map(|tx| {
				log::trace!(target:"basic_authorship", "decrypting singly encrypted call INPUT : {:?}", tx.data);
				let decrypted_msg = aes_decrypt(&aes_key, &tx.data).unwrap();
				log::trace!(target:"basic_authorship", "decrypting singly encrypted call OUTPUT: {:?}", decrypted_msg);
				api.create_submit_decrypted_transaction(&self.parent_id, tx.tx_id, decrypted_msg, 500000000).unwrap()
			});

			let singly_encrypted_inherents = doubly_encrypted_txs.into_iter().map(|tx| {
				log::trace!(target:"basic_authorship", "decrypting doubly encrypted call INPUT : {:?}", tx.data);
				let decrypted_msg = aes_decrypt(&aes_key, &tx.data).unwrap();
				log::trace!(target:"basic_authorship", "decrypting doubly encrypted call OUTPUT: {:?}", decrypted_msg);
				api.create_submit_singly_encrypted_transaction(&self.parent_id, tx.tx_id, decrypted_msg).unwrap()
			});
			decrypted_inherents.chain(singly_encrypted_inherents).collect()
		}else{
			vec![]
		};


		let (seed, inherents) = block_builder.create_inherents(inherent_data.clone())?;
		for inherent in inherents.into_iter().chain(decrypted_inherents.into_iter()){
			match block_builder.push(inherent) {
				Err(ApplyExtrinsicFailed(Validity(e))) if e.exhausted_resources() => {
					warn!("⚠️  Dropping non-mandatory inherent from overweight block.")
				}
				Err(ApplyExtrinsicFailed(Validity(e))) if e.was_mandatory() => {
					error!("❌️ Mandatory inherent extrinsic returned error. Block cannot be produced.");
					Err(ApplyExtrinsicFailed(Validity(e)))?
				}
				Err(e) => {
					warn!("❗️ Inherent extrinsic returned unexpected error: {}. Dropping.", e);
				}
				Ok(_) => {}
			}
		}

		// proceed with transactions
		let block_timer = time::Instant::now();
		let mut skipped = 0;
		let unqueue_invalid = Rc::new(RefCell::new(Vec::new()));
		let invalid = unqueue_invalid.clone();
		let parent_number = self.parent_number;
		let transaction_pool = self.transaction_pool.clone();
		let now = self.now;
		debug!("Attempting to push transactions from the pool.");
		debug!("Pool status: {:?}", self.transaction_pool.status());
		block_builder.consume_valid_transactions(
			Box::new(move |at, api| {
				let pending_iterator = match executor::block_on(future::select(
					transaction_pool.ready_at(parent_number),
					futures_timer::Delay::new(deadline.saturating_duration_since((now)()) / 8),
				)) {
					Either::Left((iterator, _)) => iterator,
					Either::Right(_) => {
						log::warn!(
							"Timeout fired waiting for transaction pool at block #{}. Proceeding with production.",
							parent_number,
						);
						transaction_pool.ready()
					}
				};

				let mut extrinsics: Vec<_> = Vec::new();
				for p in pending_iterator {
					let pending_tx_data = p.data().clone();
					let pending_tx_hash = p.hash().clone();
					let execution_status = api.execute_in_transaction(|_| {
						match api.apply_extrinsic_with_context(
							at,
							ExecutionContext::BlockConstruction,
							pending_tx_data.clone(),
						) {
							Ok(Ok(_)) => TransactionOutcome::Commit(Ok(())),
							Ok(Err(tx_validity)) => TransactionOutcome::Rollback(Err(Validity(tx_validity).into())),
							Err(e) => TransactionOutcome::Rollback(Err(e)),
						}
					});

					match execution_status {
						Ok(()) => {
							extrinsics.push(pending_tx_data);
							debug!("[{:?}] Pushed to the block.", pending_tx_hash);
						}
						Err(ApplyExtrinsicFailed(Validity(e))) if e.exhausted_resources() => {
							if skipped < MAX_SKIPPED_TRANSACTIONS {
								skipped += 1;
								debug!(
									"Block seems full, but will try {} more transactions before quitting.",
									MAX_SKIPPED_TRANSACTIONS - skipped,
								);
							} else {
								debug!("Block is full, proceed with proposing.");
								break;
							}
						}
						Err(e) if skipped > 0 => {
							trace!(
								"[{:?}] Ignoring invalid transaction when skipping: {}",
								pending_tx_hash,
								e
							);
						}
						Err(e) => {
							debug!("[{:?}] Invalid transaction: {}", pending_tx_hash, e);
							invalid.borrow_mut().push(pending_tx_hash);
						}
					};
				}
				extrinsics
			}),
			inherent_data,
		)?;

		self.transaction_pool
			.remove_invalid(unqueue_invalid.borrow().as_slice());

		let (block, storage_changes, proof) = block_builder.build(seed)?.into_inner();

		self.metrics.report(
			|metrics| {
				metrics.number_of_transactions.set(block.extrinsics().len() as u64);
				metrics.block_constructed.observe(block_timer.elapsed().as_secs_f64());
			}
		);

		info!("🎁 Prepared block for proposing at {} [hash: {:?}; parent_hash: {}; extrinsics ({}): [{}]]",
			block.header().number(),
			<Block as BlockT>::Hash::from(block.header().hash()),
			block.header().parent_hash(),
			block.extrinsics().len(),
			block.extrinsics()
				.iter()
				.map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
				.collect::<Vec<_>>()
				.join(", ")
		);
		telemetry!(CONSENSUS_INFO; "prepared_block_for_proposing";
			"number" => ?block.header().number(),
			"hash" => ?<Block as BlockT>::Hash::from(block.header().hash()),
		);

		if Decode::decode(&mut block.encode().as_slice()).as_ref() != Ok(&block) {
			error!("Failed to verify block encoding/decoding");
		}

		if let Err(err) = evaluation::evaluate_initial(&block, &self.parent_hash, self.parent_number) {
			error!("Failed to evaluate authored block: {:?}", err);
		}

		Ok(Proposal { block, proof, storage_changes })
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use pallet_random_seed::RandomSeedInherentDataProvider;
	use parking_lot::Mutex;
	use sc_client_api::Backend;
	use sc_transaction_pool::BasicPool;
	use sp_api::Core;
	use sp_blockchain::HeaderBackend;
	use sp_consensus::{BlockOrigin, Proposer};
	use sp_inherents::{InherentData, ProvideInherentData};
	use sp_runtime::{DigestItem, traits::NumberFor};
	use sp_transaction_pool::{ChainEvent, MaintainedTransactionPool, TransactionSource};
	use sc_keystore::Store;
    use sc_transaction_pool::FullChainApi;
    use ecies::utils::{aes_encrypt, encapsulate};
    use sp_encrypted_tx::ExtrinsicType;
    use std::collections::HashSet;
    use sc_consensus_babe::{PreDigest, CompatibleDigestItem, SecondaryPlainPreDigest};

	use substrate_test_runtime_client::{
		prelude::*,
		runtime::{Extrinsic, Transfer, Block},
		TestClientBuilder, TestClientBuilderExt,
	};
	use sp_runtime::traits::Block as BlockT;

	const SOURCE: TransactionSource = TransactionSource::External;

	/// inject shuffling seed that is mandatory in mangata
	fn create_inherents() -> InherentData {
		let mut data: InherentData = Default::default();
		RandomSeedInherentDataProvider(Default::default())
			.provide_inherent_data(&mut data)
			.unwrap();

		sp_ignore_tx::IgnoreTXInherentDataProvider(false)
			.provide_inherent_data(&mut data)
			.unwrap();
		data
	}

    fn create_digest() -> DigestFor<Block>{
        let mut digests : DigestFor<Block> = Default::default();
        let babe_pre = sc_consensus_babe::PreDigest::SecondaryPlain(sc_consensus_babe::SecondaryPlainPreDigest{
            authority_index: substrate_test_runtime::ALICE_COLLATOR_ID,
            slot_number: Default::default(),
        });
        digests.push(DigestItem::babe_pre_digest(babe_pre));
        digests
    }

	fn extrinsic(nonce: u64) -> Extrinsic {
		Transfer {
			amount: Default::default(),
			nonce,
			from: AccountKeyring::Alice.into(),
			to: Default::default(),
		}.into_signed_tx()
	}

	fn chain_event<B: BlockT>(header: B::Header) -> ChainEvent<B>
		where NumberFor<B>: From<u64>
	{
		ChainEvent::NewBestBlock {
			hash: header.hash(),
			tree_route: None,
		}
	}

	fn create_key_store() -> KeyStorePtr{
		let store = Store::new_in_memory();

		let secret_uri = "//Alice";
		store.write().insert_ephemeral_from_seed_by_type::<sp_core::ecdsa::Pair>(
			secret_uri,
			KeyTypeId(*b"xxtx"),
		).expect("Inserts unknown key");
        store
	}



	#[test]
	fn should_cease_building_block_when_deadline_is_reached() {
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			None,
			spawner,
			client.clone(),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![extrinsic(0), extrinsic(1)])
		).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header")
			))
		);

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());

		let cell = Mutex::new((false, time::Instant::now()));
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || {
				let mut value = cell.lock();
				if !value.0 {
					value.0 = true;
					return value.1;
				}
				let old = value.1;
				let new = old + time::Duration::from_secs(2);
				*value = (true, new);
				old
			}),
		);

		// when
		let deadline = time::Duration::from_secs(3);
		let block = futures::executor::block_on(proposer.propose(
			create_inherents(),
			create_digest(),
			deadline,
			RecordProof::No,
		))
		.map(|r| r.block)
		.unwrap();

		// then
		// block should have some extrinsics although we have some more in the pool.
		assert_eq!(block.extrinsics().len(), 2); // inherents only [set_timestamp, shuffling_seed]
		assert_eq!(txpool.ready().count(), 2);
	}

	#[test]
	fn should_not_panic_when_deadline_is_reached() {
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(Default::default(), None, spawner, client.clone());

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());

		let cell = Mutex::new((false, time::Instant::now()));
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || {
				let mut value = cell.lock();
				if !value.0 {
					value.0 = true;
					return value.1;
				}
				let new = value.1 + time::Duration::from_secs(160);
				*value = (true, new);
				new
			}),
		);

		let deadline = time::Duration::from_secs(1);
		futures::executor::block_on(proposer.propose(
			create_inherents(),
			create_digest(),
			deadline,
			RecordProof::No,
		))
		.map(|r| r.block)
		.unwrap();
	}

	#[test]
	// that test should be enabled when extended header will be implemented
	// the main problem is when block is executed to verify storage changes
	// it actully tries to execute extrinsics stored 
	fn proposed_storage_changes_should_match_execute_block_storage_changes() {
		let (client, backend) = TestClientBuilder::new().build_with_backend();
		let _ = backend.blockchain();
		let client = Arc::new(client);
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(Default::default(), None, spawner, client.clone());

		let genesis_hash = client.info().best_hash;
		let block_id = BlockId::Hash(genesis_hash);

		futures::executor::block_on(txpool.submit_at(&BlockId::number(0), SOURCE, vec![extrinsic(0)])).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client
					.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header"),
			)),
		);

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());

		let proposer = proposer_factory.init_with_now(
			&client.header(&block_id).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		let deadline = time::Duration::from_secs(9);
		let proposal = futures::executor::block_on(proposer.propose(
			create_inherents(),
			create_digest(),
			deadline,
			RecordProof::No,
		))
		.unwrap();

		assert_eq!(proposal.block.extrinsics().len(), 1);

		// TODO perform full validation when all required information will be stored inside
		// header
		let api = client.runtime_api();
		let mut header = proposal.block.header.clone();
		let prev_header = backend.blockchain().header(BlockId::Hash(genesis_hash)).unwrap().unwrap();
		header.set_extrinsics_root(*prev_header.extrinsics_root());
		api.execute_block(&block_id, <Block as BlockT>::new(header, vec![])).unwrap();

		let state = backend.state_at(block_id).unwrap();
		let changes_trie_state =
			backend::changes_tries_state_at_block(&block_id, backend.changes_trie_storage()).unwrap();

		let storage_changes = api
			.into_storage_changes(&state, changes_trie_state.as_ref(), genesis_hash)
			.unwrap();

		assert_eq!(
			proposal.storage_changes.transaction_storage_root,
			storage_changes.transaction_storage_root,
		);
	}

	#[test]
	fn should_not_remove_invalid_transactions_when_skipping() {
        let _ = env_logger::try_init();
		let mut client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full(
			Default::default(),
			None,
			spawner,
			client.clone(),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				extrinsic(0),
				extrinsic(1),
				Transfer {
					amount: Default::default(),
					nonce: 2,
					from: AccountKeyring::Alice.into(),
					to: Default::default(),
				}.into_resources_exhausting_tx(),
				extrinsic(3),
				Transfer {
					amount: Default::default(),
					nonce: 4,
					from: AccountKeyring::Alice.into(),
					to: Default::default(),
				}.into_resources_exhausting_tx(),
				extrinsic(5),
				extrinsic(6),
			])
		).unwrap();

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());
		let mut propose_block = |
			client: &TestClient,
			number,
			expected_block_extrinsics,
			expected_pool_transactions,
		| {
			let proposer = proposer_factory.init_with_now(
				&client.header(&BlockId::number(number)).unwrap().unwrap(),
				Box::new(move || time::Instant::now()),
			);

			// when
			let deadline = time::Duration::from_secs(9);
			let block = futures::executor::block_on(
				proposer.propose(create_inherents(), create_digest(), deadline, RecordProof::No)
			).map(|r| r.block).unwrap();

			// then
			// block should have some extrinsics although we have some more in the pool.
			assert_eq!(block.extrinsics().len(), expected_block_extrinsics);
			assert_eq!(txpool.ready().count(), expected_pool_transactions);

				block
			};

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(0u64))
					.expect("header get error")
					.expect("there should be header")
			))
		);

		// let's create one block and import it
		let block = propose_block(&client, 0, 2, 7);
        println!("{:?}", block.extrinsics());
		let block_hash = block.header().hash();
		client.import(BlockOrigin::Own, block).unwrap();

		// push one extra block - extrinsics in the pool makred as 'exhausted_resources'
		// to succeed needs to be executed as first in the processed block. Due to
		// modifications in block_builder all extrinsics from previous block are applied
		// beofre trying to validate extrinsics from the tx pool. Once we include empty
		// block in between 'exhausted_resources' extrinsic from the pool is exeucted as
		// the first one and the origin test logic is maintained
		let block = client.new_block_at(&BlockId::Hash(block_hash), Default::default(), false)
			.unwrap()
			.build(Default::default())
			.unwrap();
		client.import(BlockOrigin::Own, block.block).unwrap();

		futures::executor::block_on(
			txpool.maintain(chain_event(
				client.header(&BlockId::Number(1))
					.expect("header get error")
					.expect("there should be header")
			))
		);
		// now let's make sure that we can still make some progress
		let block = propose_block(&client, 2, 2, 5);
        println!("{:?}", block.extrinsics());
		client.import(BlockOrigin::Own, block).unwrap();
	}


    use substrate_test_runtime_client::Client;
    use substrate_test_runtime_client::sc_client_db;
	type TxPoolImpl = BasicPool< FullChainApi<Client<sc_client_db::Backend<Block>>, Block> , Block>;
	type ClientImpl = Client<sc_client_db::Backend<Block>>;

    struct BlockBuilderHelper{
        pool: Arc<TxPoolImpl>,
        client: Arc<ClientImpl>,
        block_number: u64,
    }


	impl BlockBuilderHelper{

		fn new(pool: Arc<TxPoolImpl>,
			client: Arc<ClientImpl>) -> Self{
			BlockBuilderHelper{
				pool,
				client,
				block_number: 0,
			}
		}

        fn produce_block(&self, inherent_data: InherentData, digests: DigestFor<Block>) -> sp_blockchain::Result<Block>{
			let client = self.client.clone();
			let mut proposer_factory = ProposerFactory::new(client.clone(), self.pool.clone(), None, create_key_store());
			let proposer = proposer_factory.init_with_now(
				&self.client.header(&BlockId::number(self.block_number)).unwrap().unwrap(),
				Box::new(move || time::Instant::now()),
			);

			futures::executor::block_on(
				self.pool.maintain(chain_event(
						client.header(&BlockId::Number(self.block_number))
						.expect("header get error")
						.expect("there should be header")
				))
			);

			let deadline = time::Duration::from_secs(9);
			futures::executor::block_on(
				proposer.propose(inherent_data, digests, deadline, RecordProof::No)
			).map(|r| r.block)
        }

		fn produce_and_import_block(& mut self) -> Block {
            let block = self.produce_block(create_inherents(), create_digest()).unwrap();
			let mut client = self.client.clone();
			client.import(BlockOrigin::Own, block.clone()).unwrap();
			self.block_number += 1;
			block
		}

		fn encrypt_payload_using_pub_key(&self, pub_key: &sp_core::ecdsa::Public, payload: &[u8]) -> Vec<u8>{
			let dummy_secret_key: SecretKey = SecretKey::default();
			let pub_key = PublicKey::parse_slice(pub_key.as_ref(), None).unwrap();
			let encryption_key = encapsulate(&dummy_secret_key, &pub_key).unwrap();
			aes_encrypt(&encryption_key, &payload).unwrap()
		}

	}

	#[test]
	fn inject_doubly_encrypted_tx_and_expect_singly_ecrypted_extrinsic() {
        let _ = env_logger::try_init();
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());
		let payload = b"hello world".iter().cloned().collect::<Vec<_>>();
		let collator_public_key = client.runtime_api().get_authority_public_key(&BlockId::Number(0), &substrate_test_runtime::ALICE_ACCOUNT_ID.into()).unwrap().unwrap();

		let encrypted_message = bb.encrypt_payload_using_pub_key(&collator_public_key, &payload);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: false,
					data:encrypted_message
				}
			])
		).unwrap();

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 0);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
		let extrinsic = &block.extrinsics()[0];
		assert!(
			matches!(extrinsic,
				Extrinsic::EncryptedTX(
					ExtrinsicType::<<Block as BlockT>::Hash>::SinglyEncryptedTx{
						singly_encrypted_call, ..
					}
				) if singly_encrypted_call == &payload
			)
		);

	}

	#[test]
	fn inject_multiple_doubly_encrypted_txs_and_expect_singly_ecrypted_extrinsic() {
		// env_logger::init();
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());
		let collator_public_key = client.runtime_api().get_authority_public_key(&BlockId::Number(0), &substrate_test_runtime::ALICE_ACCOUNT_ID.into()).unwrap().unwrap();
		let payload1 = b"hello world1".iter().cloned().collect::<Vec<_>>();
		let payload2 = b"hello world2".iter().cloned().collect::<Vec<_>>();

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: false,
					data: bb.encrypt_payload_using_pub_key(&collator_public_key, &payload1)
				},
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: false,
					data: bb.encrypt_payload_using_pub_key(&collator_public_key, &payload2)
				},
			])
		).unwrap();

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 2);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 0);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 2);

        let decrypted_payloads : HashSet<_> = block.extrinsics().iter()
            .map(|xt| match xt {
				Extrinsic::EncryptedTX(
					ExtrinsicType::<<Block as BlockT>::Hash>::SinglyEncryptedTx{
						singly_encrypted_call, ..
					}
                ) => { singly_encrypted_call },
                _ => { panic!("wrong extrinsic type") }
        }).collect();

        assert_eq!(HashSet::from([payload1, payload2].iter().collect()), decrypted_payloads);
	}

	#[test]
	fn inject_singly_encrypted_tx_and_expect_decrytped_transaction() {
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());
		let payload = b"hello world".iter().cloned().collect::<Vec<_>>();
		let collator_public_key = client.runtime_api().get_authority_public_key(&BlockId::Number(0), &substrate_test_runtime::ALICE_ACCOUNT_ID.into()).unwrap().unwrap();

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: bb.encrypt_payload_using_pub_key(&collator_public_key, &payload),
				}
			])
		).unwrap();

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 0);

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
		let extrinsic = &block.extrinsics()[0];
		assert!(
			matches!(extrinsic,
				Extrinsic::EncryptedTX(
					ExtrinsicType::<<Block as BlockT>::Hash>::DecryptedTx{
						decrypted_call, ..
					}
				) if decrypted_call == &payload
			)
		);

	}

	#[test]
	fn dont_panic_on_wrongly_encrypted_doubly_encrypted_tx(){
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: false,
					data: vec![1,2,3,4,5,6,7,8,9],
				}
			])
		).unwrap();

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
	}

	#[test]
	fn dont_panic_on_wrongly_encrypted_singly_encrypted_tx(){
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: vec![1,2,3,4,5,6,7,8,9],
				}
			])
		).unwrap();

		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
	}

	#[test]
	fn dont_panic_on_empty_payload_in_doubly_encrypted_tx(){
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: false,
					data: vec![],
				}
			])
		).unwrap();
		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
	}

	#[test]
	fn dont_panic_when_public_key_was_not_found(){
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut bb = BlockBuilderHelper::new(txpool.clone(), client.clone());

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: vec![],
				}
			])
		).unwrap();
		let block = bb.produce_and_import_block();
		assert_eq!(block.extrinsics().len(), 1);
	}

	#[test]
	fn fail_to_create_block_on_missing_pre_digest(){
		let _ = env_logger::try_init();
		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: vec![],
				}
			])
		).unwrap();

		assert!(
			matches!(
				futures::executor::block_on(proposer.propose(
						create_inherents(),
						Default::default(),
						time::Duration::from_secs(9),
						RecordProof::No,)
				),
				Err(sp_blockchain::Error::Backend(e)) if e == String::from("No BABE pre-runtime digest found")
			)
		);
	}

	#[test]
	fn fail_to_create_block_on_uknown_collator_id(){
		let _ = env_logger::try_init();
        let mut digests : DigestFor<Block> = Default::default();
		let unknown_autohrity_index = 10;
        digests.push(DigestItem::babe_pre_digest(
			PreDigest::SecondaryPlain(SecondaryPlainPreDigest{
				authority_index: unknown_autohrity_index,
				slot_number: Default::default(),
		})));

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: vec![],
				}
			])
		).unwrap();

		assert!(
			matches!(
				futures::executor::block_on(proposer.propose(
						create_inherents(),
						digests,
						time::Duration::from_secs(9),
						RecordProof::No,)
				),
				Err(sp_blockchain::Error::Backend(e)) if e == String::from(INVALID_COLLATOR_ID)
			)
		);
	}

	#[test]
	fn fail_to_create_block_on_uknown_collator_public_key(){
		let _ = env_logger::try_init();
        let mut digests : DigestFor<Block> = Default::default();
		let unknown_autohrity_index = 0;
        digests.push(DigestItem::babe_pre_digest(
			PreDigest::SecondaryPlain(SecondaryPlainPreDigest{
				authority_index: substrate_test_runtime::DUMMY_COLLATOR_ID,
				slot_number: Default::default(),
		})));

		// given
		let client = Arc::new(substrate_test_runtime_client::new());
		let spawner = sp_core::testing::TaskExecutor::new();
		let txpool = BasicPool::new_full( Default::default(), None, spawner, client.clone());

		let mut proposer_factory = ProposerFactory::new(client.clone(), txpool.clone(), None, create_key_store());
		let proposer = proposer_factory.init_with_now(
			&client.header(&BlockId::number(0)).unwrap().unwrap(),
			Box::new(move || time::Instant::now()),
		);

		futures::executor::block_on(
			txpool.submit_at(&BlockId::number(0), SOURCE, vec![
				Extrinsic::SubmitEncryptedTransaction{
					singly_encrypted: true,
					data: vec![],
				}
			])
		).unwrap();
				futures::executor::block_on(proposer.propose(
						create_inherents(),
						digests,
						time::Duration::from_secs(9),
						RecordProof::No,)).unwrap();

                panic!("this test should panic!");

		// assert!(
		// 	matches!(
		// 		futures::executor::block_on(proposer.propose(
		// 				create_inherents(),
		// 				digests,
		// 				time::Duration::from_secs(9),
		// 				RecordProof::No,)
		// 		),
		// 		Err(sp_blockchain::Error::Backend(e)) if e == String::from(INVALID_COLLATOR_ID)
		// 	)
		// );
	}


}
