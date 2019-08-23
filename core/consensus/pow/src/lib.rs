use std::sync::Arc;
use core::marker::PhantomData;
use client::{
	BlockOf, blockchain::ProvideCache, block_builder::api::BlockBuilder as BlockBuilderApi,
};
use sr_primitives::Justification;
use sr_primitives::generic::{BlockId, DigestItem};
use sr_primitives::traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi};
use srml_timestamp::{TimestampInherentData, InherentError as TIError};
use pow_primitives::{Seal, PowApi, Difficulty, POW_ENGINE_ID};
use primitives::H256;
use inherents::{InherentDataProviders, InherentData};
use consensus_common::{
	BlockImportParams, BlockOrigin, ForkChoiceStrategy, well_known_cache_keys::{self, Id as CacheKeyId}
};
use consensus_common::import_queue::Verifier;
use codec::{Encode, Decode};

/// Auxiliary data for PoW.
#[derive(Encode, Decode, Clone, Debug)]
pub struct PowAux {
	pub total_difficulty: Difficulty,
}

/// A verifier for PoW blocks.
pub struct PowVerifier<C> {
	client: Arc<C>,
	inherent_data_providers: inherents::InherentDataProviders,
}

impl<C> PowVerifier<C> {
	fn check_header<B: BlockT<Hash=H256>>(
		&self,
		mut header: B::Header,
		block_id: BlockId<B>,
	) -> Result<(B::Header, Difficulty, DigestItem<H256>), String> where
		C: ProvideRuntimeApi, C::Api: PowApi<B>,
	{
		let hash = header.hash();

		let (seal, inner_seal) = match header.digest_mut().pop() {
			Some(DigestItem::Seal(id, seal)) => {
				if id == POW_ENGINE_ID {
					(DigestItem::Seal(id, seal.clone()), seal)
				} else {
					return Err(format!("Header uses the wrong engine {:?}", id))
				}
			},
			_ => return Err(format!("Header {:?} is unsealed", hash)),
		};

		let pre_hash = header.hash();

		let difficulty = self.client.runtime_api().verify(
			&block_id,
			&pre_hash,
			&inner_seal,
		).map_err(|e| format!("{:?}", e))?;

		Ok((header, difficulty, seal))
	}

	fn check_inherents<B: BlockT<Hash=H256>>(
		&self,
		block: B,
		block_id: BlockId<B>,
		inherent_data: InherentData,
		timestamp_now: u64,
	) -> Result<(), String> where
		C: ProvideRuntimeApi, C::Api: BlockBuilderApi<B>
	{
		const MAX_TIMESTAMP_DRIFT_SECS: u64 = 60;

		let inherent_res = self.client.runtime_api().check_inherents(
			&block_id,
			block,
			inherent_data,
		).map_err(|e| format!("{:?}", e))?;

		if !inherent_res.ok() {
			inherent_res
				.into_errors()
				.try_for_each(|(i, e)| match TIError::try_from(&i, &e) {
					Some(TIError::ValidAtTimestamp(timestamp)) => {
						if timestamp > timestamp_now + MAX_TIMESTAMP_DRIFT_SECS {
							return Err("Rejecting block too far in future".into());
						}

						Ok(())
					},
					Some(TIError::Other(e)) => Err(e.into()),
					None => Err(self.inherent_data_providers.error_to_string(&i, &e)),
				})
		} else {
			Ok(())
		}
	}
}

impl<B: BlockT<Hash=H256>, C> Verifier<B> for PowVerifier<C> where
	C: ProvideRuntimeApi + Send + Sync + client::backend::AuxStore + ProvideCache<B> + BlockOf,
	C::Api: BlockBuilderApi<B> + PowApi<B>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let mut inherent_data = self.inherent_data_providers
			.create_inherent_data().map_err(String::from)?;
		let timestamp_now = inherent_data.timestamp_inherent_data().map_err(String::from)?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();

		let (checked_header, difficulty, seal) = self.check_header::<B>(
			header,
			BlockId::Hash(parent_hash),
		)?;

		if let Some(inner_body) = body.take() {
			let block = B::new(checked_header.clone(), inner_body);

			self.check_inherents(
				block.clone(),
				BlockId::Hash(parent_hash),
				inherent_data,
				timestamp_now
			)?;

			let (_, inner_body) = block.deconstruct();
			body = Some(inner_body);
		}

		let import_block = BlockImportParams {
			origin,
			header: checked_header,
			post_digests: vec![seal],
			body,
			finalized: false,
			justification,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		};

		Ok((import_block, None))
	}
}
