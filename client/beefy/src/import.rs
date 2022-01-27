use std::{collections::HashMap, marker::PhantomData, sync::Arc};

use sc_consensus::{
	BlockCheckParams, BlockImport, BlockImportParams, ImportResult, JustificationImport,
};

use sc_client_api::backend::Backend;
use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::well_known_cache_keys;
use sp_consensus::Error as ConsensusError;
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	Justification,
};

use beefy_primitives::{
	crypto::{AuthorityId, Signature},
	BeefyApi, ConsensusLog, ValidatorSet, BEEFY_ENGINE_ID,
};

use crate::{
	justification::decode_and_verify_justification, notification::BeefyJustificationSender,
	Client as BeefyClient,
};

/// Checks the given header for a consensus digest signalling a beefy authority set change
/// and extracts it.
fn find_beefy_authority_set_change<B: BlockT>(
	header: &B::Header,
) -> Option<ValidatorSet<AuthorityId>> {
	let id = OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID);

	let filter_log = |log: ConsensusLog<AuthorityId>| match log {
		ConsensusLog::AuthoritiesChange(change) => Some(change),
		_ => None,
	};

	// find the first consensus digest with the right ID which converts to
	// the right kind of consensus log.
	header.digest().convert_first(|l| l.try_to(id).and_then(filter_log))
}

/// A block-import handler for BEEFY.
///
/// This scans each imported block for BEEFY justifications and verifies them.
/// Wraps a type `inner` that implements [`BlockImport`] and ultimately defers to it.
pub struct BeefyBlockImport<Backend, Block: BlockT, Client, I> {
	client: Arc<Client>,
	inner: I,
	justification_sender: BeefyJustificationSender<NumberFor<Block>, Signature>,
	_phantom: PhantomData<Backend>,
}

impl<BE, Block: BlockT, Client, I: Clone> Clone for BeefyBlockImport<BE, Block, Client, I> {
	fn clone(&self) -> Self {
		BeefyBlockImport {
			client: self.client.clone(),
			inner: self.inner.clone(),
			justification_sender: self.justification_sender.clone(),
			_phantom: PhantomData,
		}
	}
}

#[async_trait::async_trait]
impl<BE, Block: BlockT, Client, I> BlockImport<Block> for BeefyBlockImport<BE, Block, Client, I>
where
	BE: Backend<Block>,
	I: BlockImport<
			Block,
			Error = ConsensusError,
			Transaction = sp_api::TransactionFor<Client, Block>,
		> + Send
		+ Sync,
	Client: BeefyClient<Block, BE>,
	Client::Api: BeefyApi<Block>,
	for<'a> &'a Client:
		BlockImport<Block, Error = ConsensusError, Transaction = TransactionFor<Client, Block>>,
	TransactionFor<Client, Block>: 'static,
{
	type Error = ConsensusError;
	type Transaction = TransactionFor<Client, Block>;

	async fn import_block(
		&mut self,
		block: BlockImportParams<Block, Self::Transaction>,
		new_cache: HashMap<well_known_cache_keys::Id, Vec<u8>>,
	) -> Result<ImportResult, Self::Error> {
		let hash = block.post_hash();
		let number = *block.header.number();
		let justifications = block.justifications.clone();
		// If this block contains a beefy authority set change then it must have a beefy
		// justification
		let change = find_beefy_authority_set_change::<Block>(&block.header);
		// Run inner block import
		let import_result = self.inner.import_block(block, new_cache).await?;
		// Try importing beefy justification
		let beefy_justification =
			justifications.and_then(|just| just.into_justification(BEEFY_ENGINE_ID));

		if change.is_some() && beefy_justification.is_none() {
			return Err(ConsensusError::ClientImport(
				"Missing beefy justification in authority set change block".to_string(),
			))
		}
		if let Some(beefy_justification) = beefy_justification {
			self.import_justification(hash, number, (BEEFY_ENGINE_ID, beefy_justification))?;
		}
		Ok(import_result)
	}

	async fn check_block(
		&mut self,
		block: BlockCheckParams<Block>,
	) -> Result<ImportResult, Self::Error> {
		self.inner.check_block(block.clone()).await
	}
}

#[async_trait::async_trait]
impl<BE, Block: BlockT, Client, I> JustificationImport<Block>
	for BeefyBlockImport<BE, Block, Client, I>
where
	BE: Backend<Block>,
	Client: BeefyClient<Block, BE> + ProvideRuntimeApi<Block>,
	Client::Api: BeefyApi<Block>,
	I: JustificationImport<Block, Error = ConsensusError> + Send + Sync,
{
	type Error = ConsensusError;

	async fn on_start(&mut self) -> Vec<(Block::Hash, NumberFor<Block>)> {
		self.inner.on_start().await
	}

	async fn import_justification(
		&mut self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), Self::Error> {
		// Try Importing Beefy justification
		BeefyBlockImport::import_justification(self, hash, number, justification.clone())?;
		// Importing for inner BlockImport
		self.inner.import_justification(hash, number, justification).await
	}
}

impl<BE, Block: BlockT, Client, I> BeefyBlockImport<BE, Block, Client, I>
where
	BE: Backend<Block>,
	Client: BeefyClient<Block, BE> + ProvideRuntimeApi<Block>,
	Client::Api: BeefyApi<Block>,
{
	/// Import a block justification.
	fn import_justification(
		&mut self,
		hash: Block::Hash,
		number: NumberFor<Block>,
		justification: Justification,
	) -> Result<(), ConsensusError> {
		if justification.0 != BEEFY_ENGINE_ID {
			return Ok(())
		}

		// This function assumes the Block should have already been imported
		let at = BlockId::hash(hash);
		let validator_set = self
			.client
			.runtime_api()
			.validator_set(&at)
			.map_err(|e| ConsensusError::ClientImport(e.to_string()))?;

		if let Some(validator_set) = validator_set {
			let encoded_proof = justification.1;
			let _proof = decode_and_verify_justification::<Block>(
				number,
				&encoded_proof[..],
				&validator_set,
			)?;
		} else {
			return Err(ConsensusError::ClientImport("Empty validator set".to_string()))
		}
		Ok(())
	}
}

impl<BE, Block: BlockT, Client, I> BeefyBlockImport<BE, Block, Client, I> {
	/// Create  a new BeefyBlockImport
	pub(crate) fn new(
		client: Arc<Client>,
		inner: I,
		justification_sender: BeefyJustificationSender<NumberFor<Block>, Signature>,
	) -> BeefyBlockImport<BE, Block, Client, I> {
		BeefyBlockImport { inner, client, justification_sender, _phantom: PhantomData }
	}
}
