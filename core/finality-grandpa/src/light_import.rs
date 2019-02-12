// Copyright 2019 Parity Technologies (UK) Ltd.
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

use std::sync::Arc;
use parking_lot::RwLock;

use client::{
	CallExecutor, Client,
	backend::Backend,
	blockchain::HeaderBackend,
	error::Error as ClientError, error::ErrorKind as ClientErrorKind,
	light::fetcher::{FetchChecker, RemoteCallRequest},
};
use codec::{Encode, Decode};
use consensus_common::{
	import_queue::Verifier,
	BlockOrigin, BlockImport, FinalityProofImport, ImportBlock, ImportResult,
	Error as ConsensusError, ErrorKind as ConsensusErrorKind
};
use runtime_primitives::Justification;
use runtime_primitives::traits::{
	NumberFor, Block as BlockT, Header as HeaderT, ProvideRuntimeApi,
	DigestItem, DigestFor, DigestItemFor,
};
use fg_primitives::GrandpaApi;
use runtime_primitives::generic::BlockId;
use substrate_primitives::{H256, Ed25519AuthorityId, Blake2Hasher};

use {load_consensus_changes, canonical_at_height, ConsensusChanges, GrandpaJustification};

/// LightAuthoritySet is saved under this key in aux storage.
const LIGHT_AUTHORITY_SET_KEY: &[u8] = b"grandpa_voters";
/// ConsensusChanges is saver under this key in aux storage.
const LIGHT_CONSENSUS_CHANGES_KEY: &[u8] = b"grandpa_consensus_changes";

/// Create light block importer.
pub fn light_block_import<B, E, Block: BlockT<Hash=H256>, RA, PRA>(
	client: Arc<Client<B, E, Block, RA>>,
	fetch_checker: Arc<FetchChecker<Block>>,
	api: Arc<PRA>,
) -> Result<GrandpaLightBlockImport<B, E, Block, RA>, ClientError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>,
{
	use runtime_primitives::traits::Zero;
	let authority_set = match Backend::get_aux(&**client.backend(), LIGHT_AUTHORITY_SET_KEY)? {
		None => {
			info!(target: "afg", "Loading GRANDPA authorities \
				from genesis on what appears to be first startup.");

			// no authority set on disk: fetch authorities from genesis state
			let genesis_authorities = api.runtime_api().grandpa_authorities(&BlockId::number(Zero::zero()))?;

			let authority_set = LightAuthoritySet::genesis(genesis_authorities);
			let encoded = authority_set.encode();
			Backend::insert_aux(&**client.backend(), &[(LIGHT_AUTHORITY_SET_KEY, &encoded[..])], &[])?;

			authority_set
		},
		Some(raw) => LightAuthoritySet::decode(&mut &raw[..])
			.ok_or_else(|| ::client::error::ErrorKind::Backend(
				format!("GRANDPA authority set kept in invalid format")
			))?
			.into(),
	};

	let consensus_changes = load_consensus_changes(&*client, LIGHT_CONSENSUS_CHANGES_KEY)?;

	Ok(GrandpaLightBlockImport {
		client,
		fetch_checker,
		data: Arc::new(RwLock::new(LightImportData {
			authority_set,
			consensus_changes,
		})),
	})
}

/// A light block-import handler for GRANDPA.
///
/// It is responsible for:
/// - checking GRANDPA justifications;
/// - fetching finality proofs for blocks that are enacting consensus changes.
pub struct GrandpaLightBlockImport<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	fetch_checker: Arc<FetchChecker<Block>>,
	data: Arc<RwLock<LightImportData<Block>>>,
}

/// Mutable data of light block importer.
struct LightImportData<Block: BlockT<Hash=H256>> {
	authority_set: LightAuthoritySet,
	consensus_changes: ConsensusChanges<Block::Hash, NumberFor<Block>>,
}

/// Latest authority set tracker.
#[derive(Debug, Encode, Decode)]
struct LightAuthoritySet {
	set_id: u64,
	authorities: Vec<(Ed25519AuthorityId, u64)>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA> BlockImport<Block>
	for GrandpaLightBlockImport<B, E, Block, RA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
{
	type Error = ConsensusError;

	fn import_block(&self, block: ImportBlock<Block>, new_authorities: Option<Vec<Ed25519AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		do_import_block(&*self.client, &mut *self.data.write(), block, new_authorities)
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA> FinalityProofImport<Block>
	for GrandpaLightBlockImport<B, E, Block, RA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		RA: Send + Sync,
{
	type Error = ConsensusError;

	fn on_start(&self, link: &::consensus_common::import_queue::Link<Block>) {
		let chain_info = match self.client.info() {
			Ok(info) => info.chain,
			_ => return,
		};

		let data = self.data.read();
		for (pending_number, pending_hash) in data.consensus_changes.pending_changes() {
			if *pending_number > chain_info.finalized_number && *pending_number <= chain_info.best_number {
				link.request_finality_proof(pending_hash, *pending_number);
			}
		}
	}

	fn import_finality_proof(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		finality_proof: Vec<u8>,
		verifier: &Verifier<Block>,
	) -> Result<(), Self::Error> {
		do_import_finality_proof(&*self.client, &*self.fetch_checker, &mut *self.data.write(), hash, number, finality_proof, verifier)
	}
}


impl LightAuthoritySet {
	/// Get a genesis set with given authorities.
	pub fn genesis(initial: Vec<(Ed25519AuthorityId, u64)>) -> Self {
		LightAuthoritySet {
			set_id: 0,
			authorities: initial,
		}
	}

	/// Get latest set id.
	pub fn set_id(&self) -> u64 {
		self.set_id
	}

	/// Get latest authorities set.
	pub fn authorities(&self) -> Vec<(Ed25519AuthorityId, u64)> {
		self.authorities.clone()
	}

	/// Set new authorities set.
	pub fn update(&mut self, set_id: u64, authorities: Vec<(Ed25519AuthorityId, u64)>) {
		self.set_id = set_id;
		std::mem::replace(&mut self.authorities, authorities);
	}
}

/// Try to import new block.
fn do_import_block<B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	data: &mut LightImportData<Block>,
	mut block: ImportBlock<Block>,
	new_authorities: Option<Vec<Ed25519AuthorityId>>,
) -> Result<ImportResult, ConsensusError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		NumberFor<Block>: grandpa::BlockNumberOps,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
{
	let hash = block.post_header().hash();
	let number = block.header.number().clone();

	// we don't want to finalize on `inner.import_block`
	let justification = block.justification.take();
	let enacts_consensus_change = new_authorities.is_some();
	let import_result = client.import_block(block, new_authorities);

	let import_result = {
		match import_result {
			Ok(ImportResult::Queued) => ImportResult::Queued,
			Ok(r) => return Ok(r),
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
		}
	};

	match justification {
		Some(justification) => {
			do_import_justification(client, data, hash, number, justification)?;
			Ok(import_result)
		},
		None if enacts_consensus_change => {
			// remember that we need justification for this block
			data.consensus_changes.note_change((number, hash));
			Ok(ImportResult::NeedsJustification)
		},
		None => Ok(import_result),
	}
}

/// Try to import finality proof.
fn do_import_finality_proof<B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	fetch_checker: &FetchChecker<Block>,
	data: &mut LightImportData<Block>,
	_hash: Block::Hash,
	_number: NumberFor<Block>,
	finality_proof: Vec<u8>,
	verifier: &Verifier<Block>,
) -> Result<(), ConsensusError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		DigestFor<Block>: Encode,
		DigestItemFor<Block>: DigestItem<AuthorityId=Ed25519AuthorityId>,
		NumberFor<Block>: grandpa::BlockNumberOps,
{
	// TODO: ensure that the proof is for non-finalized block
	let authority_set_id = data.authority_set.set_id();
	let authorities = data.authority_set.authorities();
	let finality_effects = ::finality_proof::check_finality_proof(
		&*client.backend().blockchain(),
		authority_set_id,
		authorities,
		|hash, header, authorities_proof| {
			let request = RemoteCallRequest {
				block: hash,
				header,
				method: "GrandpaApi_grandpa_authorities".into(),
				call_data: vec![],
				retry_count: None,
			};
			
			fetch_checker.check_execution_proof(&request, authorities_proof)
				.and_then(|authorities| {
					let authorities: Vec<(Ed25519AuthorityId, u64)> = Decode::decode(&mut &authorities[..])
						.ok_or_else(|| ClientError::from(ClientErrorKind::CallResultDecode(
							"failed to decode GRANDPA authorities set proof".into(),
						)))?;
					Ok(authorities.into_iter().collect())
				})
		},
		finality_proof,
	).map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?;

	// try to import all new headers
	let block_origin = BlockOrigin::NetworkBroadcast;
	for header_to_import in finality_effects.headers_to_import {
		let (block_to_import, new_authorities) = verifier.verify(block_origin, header_to_import, None, None)?;
		assert!(block_to_import.justification.is_none(), "We have passed None as justification to verifier.verify");
		do_import_block(client, data, block_to_import, new_authorities)?;
	}

	// try to import latest justification
	let finalized_block_hash = finality_effects.block;
	let finalized_block_number = client.backend().blockchain()
		.expect_block_number_from_id(&BlockId::Hash(finality_effects.block))
		.map_err(|e| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string())))?;
	do_finalize_block(client, data, finalized_block_hash, finalized_block_number, finality_effects.justification.encode())?;

	// apply new authorities set
	data.authority_set.update(
		finality_effects.new_set_id,
		finality_effects.new_authorities,
	);

	Ok(())
}

/// Try to import justification.
fn do_import_justification<B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	data: &mut LightImportData<Block>,
	hash: Block::Hash,
	number: NumberFor<Block>,
	justification: Justification,
) -> Result<ImportResult, ConsensusError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		NumberFor<Block>: grandpa::BlockNumberOps,
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
	let justification = GrandpaJustification::<Block>::decode_and_verify(
		&justification,
		authority_set_id,
		&data.authority_set.authorities().into_iter().collect(),
	);

	// BadJustification error means that justification has been successfully decoded, but
	// it isn't valid within current authority set
	let justification = match justification {
		Err(ClientError(ClientErrorKind::BadJustification(_), _)) => return Ok(ImportResult::NeedsFinalityProof),
		Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
		Ok(justification) => justification,
	};

	// finalize the block
	do_finalize_block(client, data, hash, number, justification.encode())
}

/// Finalize the block.
fn do_finalize_block<B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	data: &mut LightImportData<Block>,
	hash: Block::Hash,
	number: NumberFor<Block>,
	justification: Justification,
) -> Result<ImportResult, ConsensusError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		NumberFor<Block>: grandpa::BlockNumberOps,
{
	// finalize the block
	client.finalize_block(BlockId::Hash(hash), Some(justification), true).map_err(|e| {
		warn!(target: "finality", "Error applying finality to block {:?}: {:?}", (hash, number), e);
		ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string()))
	})?;

	// forget obsoleted consensus changes
	let consensus_finalization_res = data.consensus_changes
		.finalize((number, hash), |at_height| canonical_at_height(&client, (hash, number), at_height));
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

	Ok(ImportResult::Queued)
}

/// Insert into aux store. If failed, return error && show inconsistency warning.
fn require_insert_aux<T: Encode, B, E, Block: BlockT<Hash=H256>, RA>(
	client: &Client<B, E, Block, RA>,
	key: &[u8],
	value: &T,
	value_type: &str,
) -> Result<(), ConsensusError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
{
	let backend = &**client.backend();
	let encoded = value.encode();
	let update_res = Backend::insert_aux(backend, &[(key, &encoded[..])], &[]);
	if let Err(error) = update_res {
		return Err(on_post_finalization_error(error, value_type));
	}

	Ok(())
}

/// Display inconsistency warning.
fn on_post_finalization_error(error: ClientError, value_type: &str) -> ConsensusError {
	warn!(target: "finality", "Failed to write updated {} to disk. Bailing.", value_type);
	warn!(target: "finality", "Node is in a potentially inconsistent state.");
	ConsensusError::from(ConsensusErrorKind::ClientImport(error.to_string()))
}
