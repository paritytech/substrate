// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::collections::HashMap;
use std::sync::Arc;
use log::{info, trace, warn};
use parking_lot::RwLock;
use sc_client::Client;
use sc_client_api::{CallExecutor, backend::{AuxStore, Backend, Finalizer, TransactionFor}};
use sp_blockchain::{HeaderBackend, Error as ClientError, well_known_cache_keys};
use parity_scale_codec::{Encode, Decode};
use sp_consensus::{
	import_queue::Verifier,
	BlockOrigin, BlockImport, FinalityProofImport, BlockImportParams, ImportResult, ImportedAux,
	BlockCheckParams, Error as ConsensusError,
};
use sc_network::config::{BoxFinalityProofRequestBuilder, FinalityProofRequestBuilder};
use sp_runtime::Justification;
use sp_runtime::traits::{NumberFor, Block as BlockT, Header as HeaderT, DigestFor};
use sp_finality_grandpa::{self, AuthorityList};
use sp_runtime::generic::BlockId;

use crate::GenesisAuthoritySetProvider;
use crate::aux_schema::load_decode;
use crate::consensus_changes::ConsensusChanges;
use crate::environment::canonical_at_height;
use crate::finality_proof::{
	AuthoritySetForFinalityChecker, ProvableJustification, make_finality_proof_request,
};
use crate::justification::GrandpaJustification;

/// LightAuthoritySet is saved under this key in aux storage.
const LIGHT_AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";
/// ConsensusChanges is saver under this key in aux storage.
const LIGHT_CONSENSUS_CHANGES_KEY: &[u8] = b"grandpa_consensus_changes";

/// Create light block importer.
pub fn light_block_import<B, E, Block: BlockT, RA>(
	client: Arc<Client<B, E, Block, RA>>,
	backend: Arc<B>,
	genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
	authority_set_provider: Arc<dyn AuthoritySetForFinalityChecker<Block>>,
) -> Result<GrandpaLightBlockImport<B, E, Block, RA>, ClientError>
	where
		B: Backend<Block> + 'static,
		E: CallExecutor<Block> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		Client<B, E, Block, RA>: AuxStore,
{
	let info = client.info();
	let import_data = load_aux_import_data(
		info.finalized_hash,
		&*client,
		genesis_authorities_provider,
	)?;
	Ok(GrandpaLightBlockImport {
		client,
		backend,
		authority_set_provider,
		data: Arc::new(RwLock::new(import_data)),
	})
}

/// A light block-import handler for GRANDPA.
///
/// It is responsible for:
/// - checking GRANDPA justifications;
/// - fetching finality proofs for blocks that are enacting consensus changes.
pub struct GrandpaLightBlockImport<B, E, Block: BlockT, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	backend: Arc<B>,
	authority_set_provider: Arc<dyn AuthoritySetForFinalityChecker<Block>>,
	data: Arc<RwLock<LightImportData<Block>>>,
}

impl<B, E, Block: BlockT, RA> Clone for GrandpaLightBlockImport<B, E, Block, RA> {
	fn clone(&self) -> Self {
		GrandpaLightBlockImport {
			client: self.client.clone(),
			backend: self.backend.clone(),
			authority_set_provider: self.authority_set_provider.clone(),
			data: self.data.clone(),
		}
	}
}

/// Mutable data of light block importer.
struct LightImportData<Block: BlockT> {
	last_finalized: Block::Hash,
	authority_set: LightAuthoritySet,
	consensus_changes: ConsensusChanges<Block::Hash, NumberFor<Block>>,
}

/// Latest authority set tracker.
#[derive(Debug, Encode, Decode)]
struct LightAuthoritySet {
	set_id: u64,
	authorities: AuthorityList,
}

impl<B, E, Block: BlockT, RA> GrandpaLightBlockImport<B, E, Block, RA> {
	/// Create finality proof request builder.
	pub fn create_finality_proof_request_builder(&self) -> BoxFinalityProofRequestBuilder<Block> {
		Box::new(GrandpaFinalityProofRequestBuilder(self.data.clone())) as _
	}
}

impl<B, E, Block: BlockT, RA> BlockImport<Block>
	for GrandpaLightBlockImport<B, E, Block, RA> where
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
		B: Backend<Block> + 'static,
		E: CallExecutor<Block> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		RA: Send + Sync,
		for<'a> &'a Client<B, E, Block, RA>:
			BlockImport<Block, Error = ConsensusError, Transaction = TransactionFor<B, Block>>
			+ Finalizer<Block, B>
			+ AuxStore,
{
	type Error = ConsensusError;
	type Transaction = TransactionFor<B, Block>;

	fn import_block(
		&mut self,
		block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		do_import_block::<_, _, _, GrandpaJustification<Block>>(
			&*self.client, &mut *self.data.write(), block, new_cache
		)
	}

	fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.client.check_block(block)
	}
}

impl<B, E, Block: BlockT, RA> FinalityProofImport<Block>
	for GrandpaLightBlockImport<B, E, Block, RA> where
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
		B: Backend<Block> + 'static,
		E: CallExecutor<Block> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		RA: Send + Sync,
		for<'a> &'a Client<B, E, Block, RA>:
			BlockImport<Block, Error = ConsensusError, Transaction = TransactionFor<B, Block>>
			+ Finalizer<Block, B>
			+ AuxStore,
{
	type Error = ConsensusError;

	fn on_start(&mut self) -> Vec<(Block::Hash, NumberFor<Block>)> {
		let mut out = Vec::new();
		let chain_info = self.client.chain_info();

		let data = self.data.read();
		for (pending_number, pending_hash) in data.consensus_changes.pending_changes() {
			if *pending_number > chain_info.finalized_number
				&& *pending_number <= chain_info.best_number
			{
				out.push((pending_hash.clone(), *pending_number));
			}
		}

		out
	}

	fn import_finality_proof(
		&mut self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		finality_proof: Vec<u8>,
		verifier: &mut dyn Verifier<Block>,
	) -> Result<(Block::Hash, NumberFor<Block>), Self::Error> {
		do_import_finality_proof::<_, _, _, GrandpaJustification<Block>>(
			&*self.client,
			self.backend.clone(),
			&*self.authority_set_provider,
			&mut *self.data.write(),
			hash,
			number,
			finality_proof,
			verifier,
		)
	}
}

impl LightAuthoritySet {
	/// Get a genesis set with given authorities.
	pub fn genesis(initial: AuthorityList) -> Self {
		LightAuthoritySet {
			set_id: sp_finality_grandpa::SetId::default(),
			authorities: initial,
		}
	}

	/// Get latest set id.
	pub fn set_id(&self) -> u64 {
		self.set_id
	}

	/// Get latest authorities set.
	pub fn authorities(&self) -> AuthorityList {
		self.authorities.clone()
	}

	/// Set new authorities set.
	pub fn update(&mut self, set_id: u64, authorities: AuthorityList) {
		self.set_id = set_id;
		std::mem::replace(&mut self.authorities, authorities);
	}
}

struct GrandpaFinalityProofRequestBuilder<B: BlockT>(Arc<RwLock<LightImportData<B>>>);

impl<B: BlockT> FinalityProofRequestBuilder<B> for GrandpaFinalityProofRequestBuilder<B> {
	fn build_request_data(&mut self, _hash: &B::Hash) -> Vec<u8> {
		let data = self.0.read();
		make_finality_proof_request(
			data.last_finalized,
			data.authority_set.set_id(),
		)
	}
}

/// Try to import new block.
fn do_import_block<B, C, Block: BlockT, J>(
	mut client: C,
	data: &mut LightImportData<Block>,
	mut block: BlockImportParams<Block, TransactionFor<B, Block>>,
	new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
) -> Result<ImportResult, ConsensusError>
	where
		C: HeaderBackend<Block>
			+ AuxStore
			+ Finalizer<Block, B>
			+ BlockImport<Block, Transaction = TransactionFor<B, Block>>
			+ Clone,
		B: Backend<Block> + 'static,
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
		DigestFor<Block>: Encode,
		J: ProvableJustification<Block::Header>,
{
	let hash = block.post_header().hash();
	let number = block.header.number().clone();

	// we don't want to finalize on `inner.import_block`
	let justification = block.justification.take();
	let enacts_consensus_change = !new_cache.is_empty();
	let import_result = client.import_block(block, new_cache);

	let mut imported_aux = match import_result {
		Ok(ImportResult::Imported(aux)) => aux,
		Ok(r) => return Ok(r),
		Err(e) => return Err(ConsensusError::ClientImport(e.to_string()).into()),
	};

	match justification {
		Some(justification) => {
			trace!(
				target: "afg",
				"Imported block {}{}. Importing justification.",
				if enacts_consensus_change { " which enacts consensus changes" } else { "" },
				hash,
			);

			do_import_justification::<_, _, _, J>(client, data, hash, number, justification)
		},
		None if enacts_consensus_change => {
			trace!(
				target: "afg",
				"Imported block {} which enacts consensus changes. Requesting finality proof.",
				hash,
			);

			// remember that we need finality proof for this block
			imported_aux.needs_finality_proof = true;
			data.consensus_changes.note_change((number, hash));
			Ok(ImportResult::Imported(imported_aux))
		},
		None => Ok(ImportResult::Imported(imported_aux)),
	}
}

/// Try to import finality proof.
fn do_import_finality_proof<B, C, Block: BlockT, J>(
	client: C,
	backend: Arc<B>,
	authority_set_provider: &dyn AuthoritySetForFinalityChecker<Block>,
	data: &mut LightImportData<Block>,
	_hash: Block::Hash,
	_number: NumberFor<Block>,
	finality_proof: Vec<u8>,
	verifier: &mut dyn Verifier<Block>,
) -> Result<(Block::Hash, NumberFor<Block>), ConsensusError>
	where
		C: HeaderBackend<Block>
			+ AuxStore
			+ Finalizer<Block, B>
			+ BlockImport<Block, Transaction = TransactionFor<B, Block>>
			+ Clone,
		B: Backend<Block> + 'static,
		DigestFor<Block>: Encode,
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
		J: ProvableJustification<Block::Header>,
{
	let authority_set_id = data.authority_set.set_id();
	let authorities = data.authority_set.authorities();
	let finality_effects = crate::finality_proof::check_finality_proof(
		backend.blockchain(),
		authority_set_id,
		authorities,
		authority_set_provider,
		finality_proof,
	).map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

	// try to import all new headers
	let block_origin = BlockOrigin::NetworkBroadcast;
	for header_to_import in finality_effects.headers_to_import {
		let (block_to_import, new_authorities) = verifier.verify(
			block_origin,
			header_to_import,
			None,
			None,
		).map_err(|e| ConsensusError::ClientImport(e))?;
		assert!(
			block_to_import.justification.is_none(),
			"We have passed None as justification to verifier.verify",
		);

		let mut cache = HashMap::new();
		if let Some(authorities) = new_authorities {
			cache.insert(well_known_cache_keys::AUTHORITIES, authorities.encode());
		}
		do_import_block::<_, _, _, J>(
			client.clone(),
			data,
			block_to_import.convert_transaction(),
			cache,
		)?;
	}

	// try to import latest justification
	let finalized_block_hash = finality_effects.block;
	let finalized_block_number = backend.blockchain()
		.expect_block_number_from_id(&BlockId::Hash(finality_effects.block))
		.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;
	do_finalize_block(
		client,
		data,
		finalized_block_hash,
		finalized_block_number,
		finality_effects.justification.encode(),
	)?;

	// apply new authorities set
	data.authority_set.update(
		finality_effects.new_set_id,
		finality_effects.new_authorities,
	);

	Ok((finalized_block_hash, finalized_block_number))
}

/// Try to import justification.
fn do_import_justification<B, C, Block: BlockT, J>(
	client: C,
	data: &mut LightImportData<Block>,
	hash: Block::Hash,
	number: NumberFor<Block>,
	justification: Justification,
) -> Result<ImportResult, ConsensusError>
	where
		C: HeaderBackend<Block>
			+ AuxStore
			+ Finalizer<Block, B>
			+ Clone,
		B: Backend<Block> + 'static,
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
		J: ProvableJustification<Block::Header>,
{
	// with justification, we have two cases
	//
	// optimistic: the same GRANDPA authorities set has generated intermediate justification
	// => justification is verified using current authorities set + we could proceed further
	//
	// pessimistic scenario: the GRANDPA authorities set has changed
	// => we need to fetch new authorities set (i.e. finality proof) from remote node

	// first, try to behave optimistically
	let authority_set_id = data.authority_set.set_id();
	let justification = J::decode_and_verify(
		&justification,
		authority_set_id,
		&data.authority_set.authorities(),
	);

	// BadJustification error means that justification has been successfully decoded, but
	// it isn't valid within current authority set
	let justification = match justification {
		Err(ClientError::BadJustification(_)) => {
			trace!(
				target: "afg",
				"Justification for {} is not valid within current authorities set. Requesting finality proof.",
				hash,
			);

			let mut imported_aux = ImportedAux::default();
			imported_aux.needs_finality_proof = true;
			return Ok(ImportResult::Imported(imported_aux));
		},
		Err(e) => {
			trace!(
				target: "afg",
				"Justification for {} is not valid. Bailing.",
				hash,
			);

			return Err(ConsensusError::ClientImport(e.to_string()).into());
		},
		Ok(justification) => {
			trace!(
				target: "afg",
				"Justification for {} is valid. Finalizing the block.",
				hash,
			);

			justification
		},
	};

	// finalize the block
	do_finalize_block(client, data, hash, number, justification.encode())
}

/// Finalize the block.
fn do_finalize_block<B, C, Block: BlockT>(
	client: C,
	data: &mut LightImportData<Block>,
	hash: Block::Hash,
	number: NumberFor<Block>,
	justification: Justification,
) -> Result<ImportResult, ConsensusError>
	where
		C: HeaderBackend<Block>
			+ AuxStore
			+ Finalizer<Block, B>
			+ Clone,
		B: Backend<Block> + 'static,
		NumberFor<Block>: finality_grandpa::BlockNumberOps,
{
	// finalize the block
	client.finalize_block(BlockId::Hash(hash), Some(justification), true).map_err(|e| {
		warn!(target: "afg", "Error applying finality to block {:?}: {:?}", (hash, number), e);
		ConsensusError::ClientImport(e.to_string())
	})?;

	// forget obsoleted consensus changes
	let consensus_finalization_res = data.consensus_changes
		.finalize(
			(number, hash),
			|at_height| canonical_at_height(&client, (hash, number), true, at_height)
		);
	match consensus_finalization_res {
		Ok((true, _)) => require_insert_aux(
			&client,
			LIGHT_CONSENSUS_CHANGES_KEY,
			&data.consensus_changes,
			"consensus changes",
		)?,
		Ok(_) => (),
		Err(error) => return Err(on_post_finalization_error(error, "consensus changes")),
	}

	// update last finalized block reference
	data.last_finalized = hash;

	// we just finalized this block, so if we were importing it, it is now the new best
	Ok(ImportResult::imported(true))
}

/// Load light import aux data from the store.
fn load_aux_import_data<B, Block>(
	last_finalized: Block::Hash,
	aux_store: &B,
	genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
) -> Result<LightImportData<Block>, ClientError>
	where
		B: AuxStore,
		Block: BlockT,
{
	let authority_set = match load_decode(aux_store, LIGHT_AUTHORITY_SET_KEY)? {
		Some(authority_set) => authority_set,
		None => {
			info!(target: "afg", "Loading GRANDPA authorities \
				from genesis on what appears to be first startup.");

			// no authority set on disk: fetch authorities from genesis state
			let genesis_authorities = genesis_authorities_provider.get()?;

			let authority_set = LightAuthoritySet::genesis(genesis_authorities);
			let encoded = authority_set.encode();
			aux_store.insert_aux(&[(LIGHT_AUTHORITY_SET_KEY, &encoded[..])], &[])?;

			authority_set
		},
	};

	let consensus_changes = match load_decode(aux_store, LIGHT_CONSENSUS_CHANGES_KEY)? {
		Some(consensus_changes) => consensus_changes,
		None => {
			let consensus_changes = ConsensusChanges::<Block::Hash, NumberFor<Block>>::empty();

			let encoded = authority_set.encode();
			aux_store.insert_aux(&[(LIGHT_CONSENSUS_CHANGES_KEY, &encoded[..])], &[])?;

			consensus_changes
		},
	};

	Ok(LightImportData {
		last_finalized,
		authority_set,
		consensus_changes,
	})
}

/// Insert into aux store. If failed, return error && show inconsistency warning.
fn require_insert_aux<T: Encode, A: AuxStore>(
	store: &A,
	key: &[u8],
	value: &T,
	value_type: &str,
) -> Result<(), ConsensusError> {
	let encoded = value.encode();
	let update_res = store.insert_aux(&[(key, &encoded[..])], &[]);
	if let Err(error) = update_res {
		return Err(on_post_finalization_error(error, value_type));
	}

	Ok(())
}

/// Display inconsistency warning.
fn on_post_finalization_error(error: ClientError, value_type: &str) -> ConsensusError {
	warn!(target: "afg", "Failed to write updated {} to disk. Bailing.", value_type);
	warn!(target: "afg", "Node is in a potentially inconsistent state.");
	ConsensusError::ClientImport(error.to_string())
}

#[cfg(test)]
pub mod tests {
	use super::*;
	use sp_consensus::ForkChoiceStrategy;
	use sp_finality_grandpa::AuthorityId;
	use sp_core::{H256, crypto::Public};
	use substrate_test_runtime_client::sc_client::in_mem::Blockchain as InMemoryAuxStore;
	use substrate_test_runtime_client::runtime::{Block, Header};
	use crate::tests::TestApi;
	use crate::finality_proof::tests::TestJustification;

	pub struct NoJustificationsImport<B, E, Block: BlockT, RA>(
		pub GrandpaLightBlockImport<B, E, Block, RA>
	);

	impl<B, E, Block: BlockT, RA> Clone
		for NoJustificationsImport<B, E, Block, RA> where
			NumberFor<Block>: finality_grandpa::BlockNumberOps,
			B: Backend<Block> + 'static,
			E: CallExecutor<Block> + 'static + Clone + Send + Sync,
			DigestFor<Block>: Encode,
			RA: Send + Sync,
	{
		fn clone(&self) -> Self {
			NoJustificationsImport(self.0.clone())
		}
	}

	impl<B, E, Block: BlockT, RA> BlockImport<Block>
		for NoJustificationsImport<B, E, Block, RA> where
			NumberFor<Block>: finality_grandpa::BlockNumberOps,
			B: Backend<Block> + 'static,
			E: CallExecutor<Block> + 'static + Clone + Send + Sync,
			DigestFor<Block>: Encode,
			RA: Send + Sync,
			for<'a> &'a Client<B, E, Block, RA>:
				BlockImport<Block, Error = ConsensusError, Transaction = TransactionFor<B, Block>>
				+ Finalizer<Block, B>
				+ AuxStore,
	{
		type Error = ConsensusError;
		type Transaction = TransactionFor<B, Block>;

		fn import_block(
			&mut self,
			mut block: BlockImportParams<Block, Self::Transaction>,
			new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		) -> Result<ImportResult, Self::Error> {
			block.justification.take();
			self.0.import_block(block, new_cache)
		}

		fn check_block(
			&mut self,
			block: BlockCheckParams<Block>,
		) -> Result<ImportResult, Self::Error> {
			self.0.check_block(block)
		}
	}

	impl<B, E, Block: BlockT, RA> FinalityProofImport<Block>
		for NoJustificationsImport<B, E, Block, RA> where
			NumberFor<Block>: finality_grandpa::BlockNumberOps,
			B: Backend<Block> + 'static,
			E: CallExecutor<Block> + 'static + Clone + Send + Sync,
			DigestFor<Block>: Encode,
			RA: Send + Sync,
			for<'a> &'a Client<B, E, Block, RA>:
				BlockImport<Block, Error = ConsensusError, Transaction = TransactionFor<B, Block>>
				+ Finalizer<Block, B>
				+ AuxStore,
	{
		type Error = ConsensusError;

		fn on_start(&mut self) -> Vec<(Block::Hash, NumberFor<Block>)> {
			self.0.on_start()
		}

		fn import_finality_proof(
			&mut self,
			hash: Block::Hash,
			number: NumberFor<Block>,
			finality_proof: Vec<u8>,
			verifier: &mut dyn Verifier<Block>,
		) -> Result<(Block::Hash, NumberFor<Block>), Self::Error> {
			self.0.import_finality_proof(hash, number, finality_proof, verifier)
		}
	}

	/// Creates light block import that ignores justifications that came outside of finality proofs.
	pub fn light_block_import_without_justifications<B, E, Block: BlockT, RA>(
		client: Arc<Client<B, E, Block, RA>>,
		backend: Arc<B>,
		genesis_authorities_provider: &dyn GenesisAuthoritySetProvider<Block>,
		authority_set_provider: Arc<dyn AuthoritySetForFinalityChecker<Block>>,
	) -> Result<NoJustificationsImport<B, E, Block, RA>, ClientError>
		where
			B: Backend<Block> + 'static,
			E: CallExecutor<Block> + 'static + Clone + Send + Sync,
			RA: Send + Sync,
			Client<B, E, Block, RA>: BlockImport<Block, Error = ConsensusError>
				+ Finalizer<Block, B>
				+ AuxStore,
	{
		light_block_import(client, backend, genesis_authorities_provider, authority_set_provider)
			.map(NoJustificationsImport)
	}

	fn import_block(
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
		justification: Option<Justification>,
	) -> ImportResult {
		let (client, _backend) = substrate_test_runtime_client::new_light();
		let mut import_data = LightImportData {
			last_finalized: Default::default(),
			authority_set: LightAuthoritySet::genesis(vec![(AuthorityId::from_slice(&[1; 32]), 1)]),
			consensus_changes: ConsensusChanges::empty(),
		};
		let block = BlockImportParams {
			origin: BlockOrigin::Own,
			header: Header {
				number: 1,
				parent_hash: client.chain_info().best_hash,
				state_root: Default::default(),
				digest: Default::default(),
				extrinsics_root: Default::default(),
			},
			justification,
			post_digests: Vec::new(),
			body: None,
			storage_changes: None,
			finalized: false,
			auxiliary: Vec::new(),
			intermediates: Default::default(),
			fork_choice: Some(ForkChoiceStrategy::LongestChain),
			allow_missing_state: true,
			import_existing: false,
		};
		do_import_block::<_, _, _, TestJustification>(
			&client,
			&mut import_data,
			block,
			new_cache,
		).unwrap()
	}

	#[test]
	fn finality_proof_not_required_when_consensus_data_does_not_changes_and_no_justification_provided() {
		assert_eq!(import_block(HashMap::new(), None), ImportResult::Imported(ImportedAux {
			clear_justification_requests: false,
			needs_justification: false,
			bad_justification: false,
			needs_finality_proof: false,
			is_new_best: true,
			header_only: false,
		}));
	}

	#[test]
	fn finality_proof_not_required_when_consensus_data_does_not_changes_and_correct_justification_provided() {
		let justification = TestJustification((0, vec![(AuthorityId::from_slice(&[1; 32]), 1)]), Vec::new()).encode();
		assert_eq!(import_block(HashMap::new(), Some(justification)), ImportResult::Imported(ImportedAux {
			clear_justification_requests: false,
			needs_justification: false,
			bad_justification: false,
			needs_finality_proof: false,
			is_new_best: true,
			header_only: false,
		}));
	}

	#[test]
	fn finality_proof_required_when_consensus_data_changes_and_no_justification_provided() {
		let mut cache = HashMap::new();
		cache.insert(well_known_cache_keys::AUTHORITIES, vec![AuthorityId::from_slice(&[2; 32])].encode());
		assert_eq!(import_block(cache, None), ImportResult::Imported(ImportedAux {
			clear_justification_requests: false,
			needs_justification: false,
			bad_justification: false,
			needs_finality_proof: true,
			is_new_best: true,
			header_only: false,
		}));
	}

	#[test]
	fn finality_proof_required_when_consensus_data_changes_and_incorrect_justification_provided() {
		let justification = TestJustification((0, vec![]), Vec::new()).encode();
		let mut cache = HashMap::new();
		cache.insert(well_known_cache_keys::AUTHORITIES, vec![AuthorityId::from_slice(&[2; 32])].encode());
		assert_eq!(
			import_block(cache, Some(justification)),
			ImportResult::Imported(ImportedAux {
				clear_justification_requests: false,
				needs_justification: false,
				bad_justification: false,
				needs_finality_proof: true,
				is_new_best: false,
				header_only: false,
			},
		));
	}


	#[test]
	fn aux_data_updated_on_start() {
		let aux_store = InMemoryAuxStore::<Block>::new();
		let api = TestApi::new(vec![(AuthorityId::from_slice(&[1; 32]), 1)]);

		// when aux store is empty initially
		assert!(aux_store.get_aux(LIGHT_AUTHORITY_SET_KEY).unwrap().is_none());
		assert!(aux_store.get_aux(LIGHT_CONSENSUS_CHANGES_KEY).unwrap().is_none());

		// it is updated on importer start
		load_aux_import_data(Default::default(), &aux_store, &api).unwrap();
		assert!(aux_store.get_aux(LIGHT_AUTHORITY_SET_KEY).unwrap().is_some());
		assert!(aux_store.get_aux(LIGHT_CONSENSUS_CHANGES_KEY).unwrap().is_some());
	}

	#[test]
	fn aux_data_loaded_on_restart() {
		let aux_store = InMemoryAuxStore::<Block>::new();
		let api = TestApi::new(vec![(AuthorityId::from_slice(&[1; 32]), 1)]);

		// when aux store is non-empty initially
		let mut consensus_changes = ConsensusChanges::<H256, u64>::empty();
		consensus_changes.note_change((42, Default::default()));
		aux_store.insert_aux(
			&[
				(
					LIGHT_AUTHORITY_SET_KEY,
					LightAuthoritySet::genesis(
						vec![(AuthorityId::from_slice(&[42; 32]), 2)]
					).encode().as_slice(),
				),
				(
					LIGHT_CONSENSUS_CHANGES_KEY,
					consensus_changes.encode().as_slice(),
				),
			],
			&[],
		).unwrap();

		// importer uses it on start
		let data = load_aux_import_data(Default::default(), &aux_store, &api).unwrap();
		assert_eq!(data.authority_set.authorities(), vec![(AuthorityId::from_slice(&[42; 32]), 2)]);
		assert_eq!(data.consensus_changes.pending_changes(), &[(42, Default::default())]);
	}
}
