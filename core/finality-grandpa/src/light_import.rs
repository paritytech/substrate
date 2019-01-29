use std::sync::Arc;
use parking_lot::RwLock;

use client::{
	CallExecutor, Client, backend::Backend,
	error::Error as ClientError, error::ErrorKind as ClientErrorKind,
};
use client::blockchain::HeaderBackend;
use codec::{Encode, Decode};
use consensus_common::{BlockImport, JustificationImport, Error as ConsensusError, ErrorKind as ConsensusErrorKind, ImportBlock, ImportResult};
use grandpa::VoterSet;
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
	api: Arc<PRA>,
) -> Result<GrandpaLightBlockImport<B, E, Block, RA>, ClientError>
	where
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
		PRA: ProvideRuntimeApi,
		PRA::Api: GrandpaApi<Block>
{
	use runtime_primitives::traits::Zero;
	let authority_set = match Backend::get_aux(&**client.backend(), LIGHT_AUTHORITY_SET_KEY)? {
		None => {
			info!(target: "afg", "Loading GRANDPA authorities \
				from genesis on what appears to be first startup.");

			// no authority set on disk: fetch authorities from genesis state.
			// if genesis state is not available, we may be a light client, but these
			// are unsupported for following GRANDPA directly.
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
		data: Arc::new(RwLock::new(LightImportData {
			authority_set,
			consensus_changes,
		})),
	})
}

/// A light block-import handler for GRANDPA.
///
/// It is responsible for
/// - checking GRANDPA justifications;
/// - requiring GRANDPA justifications for blocks that are enacting consensus changes;
pub struct GrandpaLightBlockImport<B, E, Block: BlockT<Hash=H256>, RA> {
	client: Arc<Client<B, E, Block, RA>>,
	data: Arc<RwLock<LightImportData<Block>>>,
}

impl<B, E, Block: BlockT<Hash=H256>, RA> JustificationImport<Block>
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
				link.request_justification(pending_hash, *pending_number);
			}
		}
	}

	fn import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		self.do_import_justification(hash, number, justification)
	}
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

	fn import_block(&self, mut block: ImportBlock<Block>, new_authorities: Option<Vec<Ed25519AuthorityId>>)
		-> Result<ImportResult, Self::Error>
	{
		let hash = block.post_header().hash();
		let number = block.header.number().clone();

		// we don't want to finalize on `inner.import_block`
		let justification = block.justification.take();
		let enacts_consensus_change = new_authorities.is_some();
		let import_result = self.client.import_block(block, new_authorities);

		let import_result = {
			match import_result {
				Ok(ImportResult::Queued) => ImportResult::Queued,
				Ok(r) => return Ok(r),
				Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			}
		};

		match justification {
			Some(justification) => {
				self.do_import_justification(hash, number, justification)?;
				Ok(import_result)
			},
			None if enacts_consensus_change => {
				// remember that we need justification for this block
				self.data.write().consensus_changes.note_change((number, hash));
				Ok(ImportResult::NeedsJustification)
			},
			None => Ok(import_result),
		}
	}
}

impl<B, E, Block: BlockT<Hash=H256>, RA>
	GrandpaLightBlockImport<B, E, Block, RA> where
		NumberFor<Block>: grandpa::BlockNumberOps,
		B: Backend<Block, Blake2Hasher> + 'static,
		E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
		RA: Send + Sync,
{

	/// Import a block justification and finalize the block.
	fn do_import_justification(
		&self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		encoded_justification: Justification,
	) -> Result<(), ConsensusError> {
		let mut data = self.data.write();

		// with justification, we have two cases
		//
		// optimistic: the same GRANDPA authorities set has generated intermediate justification
		// => justification is verified using current authorities set + we could proceed further
		//
		// pessimistic scenario: the GRANDPA authorities set has changed
		// => we need to fetch new authorities set from remote node (the set ID increases by one)

		// first, try to behave optimistically
		let authority_set_id = data.authority_set.set_id();
		let justification = GrandpaJustification::<Block>::decode_and_verify(
			&encoded_justification,
			authority_set_id,
			&data.authority_set.authorities(),
		);

		// BadJustification error means that justification has been successfully decoded, but
		// it isn't valid within current authority set
		let (justification, new_grandpa_authorities) = match justification {
			Err(ClientError(ClientErrorKind::BadJustification(_), _)) => {
				let into_err = |e: ClientError| ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string()));

				// fetch GRANDPA authority set from remote node
				let header = self.client.backend().blockchain().expect_header(BlockId::Hash(hash)).map_err(into_err)?;
				let parent_block_id = BlockId::Hash(*header.parent_hash());
				let grandpa_authorities = self.client.executor().call(&parent_block_id, "GrandpaApi_grandpa_authorities", &[])
					.map_err(into_err)?;
				let grandpa_authorities: Vec<(Ed25519AuthorityId, u64)> = Decode::decode(&mut &grandpa_authorities[..])
					.ok_or_else(|| ConsensusErrorKind::ClientImport(
						ClientErrorKind::BadJustification("failed to decode GRANDPA authorities set proof".into()).to_string()
					))?;

				// ... and try to reverify justification
				let justification = GrandpaJustification::decode_and_verify(
					&encoded_justification,
					authority_set_id + 1,
					&grandpa_authorities.iter().cloned().collect(),
				).map_err(into_err)?;

				(justification, Some(grandpa_authorities))
			},
			Err(e) => return Err(ConsensusErrorKind::ClientImport(e.to_string()).into()),
			Ok(justification) => (justification, None),
		};

		// finalize the block
		self.client.finalize_block(BlockId::Hash(hash), Some(justification.encode()), true).map_err(|e| {
			warn!(target: "finality", "Error applying finality to block {:?}: {:?}", (hash, number), e);
			ConsensusError::from(ConsensusErrorKind::ClientImport(e.to_string()))
		})?;

		// forget obsoleted consensus changes
		let consensus_finalization_res = data.consensus_changes
			.finalize((number, hash), |at_height| canonical_at_height(&self.client, (hash, number), at_height));
		match consensus_finalization_res {
			Ok((true, _)) => require_insert_aux(
				&self.client,
				LIGHT_CONSENSUS_CHANGES_KEY,
				&data.consensus_changes,
				"consensus changes",
			)?,
			Ok(_) => (),
			Err(error) => return on_post_finalization_error(error, "consensus changes"),
		}

		// ... and finally update the authority set
		if let Some(new_grandpa_authorities) = new_grandpa_authorities {
			data.authority_set.update_authorities(new_grandpa_authorities);

			require_insert_aux(
				&self.client,
				LIGHT_AUTHORITY_SET_KEY,
				&data.authority_set,
				"authority set",
			)?;
		}

		Ok(())
	}
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
	pub fn authorities(&self) -> VoterSet<Ed25519AuthorityId> {
		self.authorities.iter().cloned().collect()
	}

	/// Apply new authorities set.
	pub fn update_authorities(&mut self, authorities: Vec<(Ed25519AuthorityId, u64)>) {
		self.set_id += 1;
		std::mem::replace(&mut self.authorities, authorities);
	}
}

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
		return on_post_finalization_error(error, value_type);
	}

	Ok(())
}

fn on_post_finalization_error(error: ClientError, value_type: &str) -> Result<(), ConsensusError> {
	warn!(target: "finality", "Failed to write updated {} to disk. Bailing.", value_type);
	warn!(target: "finality", "Node is in a potentially inconsistent state.");
	Err(ConsensusError::from(ConsensusErrorKind::ClientImport(error.to_string())))
}
