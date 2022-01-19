use std::{collections::HashMap, marker::PhantomData, sync::Arc};

use sc_consensus::{
	BlockCheckParams, BlockImport, BlockImportParams, ImportResult, JustificationImport,
};

use sc_client_api::backend::Backend;
use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::well_known_cache_keys;
use sp_consensus::Error as ConsensusError;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Header as HeaderT, NumberFor},
	Justification,
};

use beefy_primitives::{crypto::Signature, BeefyApi, BEEFY_ENGINE_ID};

use crate::{
	justification::decode_and_verify_justification, notification::BeefyJustificationSender,
	Client as BeefyClient,
};

/// BeefyBlockImport
/// Wraps a type `inner` that implements [`BlockImport`]
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
		// Run inner block import
		let import_result = self.inner.import_block(block, new_cache).await?;
		// Try importing beefy justification
		let beefy_justification =
			justifications.and_then(|just| just.into_justification(BEEFY_ENGINE_ID));
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
