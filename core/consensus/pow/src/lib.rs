use std::sync::{Mutex, Arc};
use std::thread;
use client::{
	BlockOf, blockchain::{HeaderBackend, ProvideCache}, block_builder::api::BlockBuilder as BlockBuilderApi, backend::AuxStore,
};
use sr_primitives::Justification;
use sr_primitives::generic::{BlockId, DigestItem};
use sr_primitives::traits::{Block as BlockT, Header as HeaderT, ProvideRuntimeApi};
use srml_timestamp::{TimestampInherentData, InherentError as TIError};
use pow_primitives::{PowApi, Difficulty, POW_ENGINE_ID};
use primitives::H256;
use inherents::{InherentDataProviders, InherentData};
use consensus_common::{
	BlockImportParams, BlockOrigin, ForkChoiceStrategy, well_known_cache_keys::Id as CacheKeyId,
	Environment, Proposer, BlockImport,
};
use consensus_common::import_queue::{BoxBlockImport, BasicQueue, Verifier};
use codec::{Encode, Decode};
use log::{debug, error, info, warn};
use futures::prelude::*;

/// Auxiliary prefix for PoW engine.
pub const POW_AUX_PREFIX: [u8; 4] = *b"PoW:";

/// Auxiliary data for PoW.
#[derive(Encode, Decode, Clone, Debug, Default)]
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
		).map_err(|e| format!("{:?}", e))?.ok_or("Invalid seal")?;

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
	C: ProvideRuntimeApi + Send + Sync + HeaderBackend<B> + AuxStore + ProvideCache<B> + BlockOf,
	C::Api: BlockBuilderApi<B> + PowApi<B>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: B::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<B::Extrinsic>>,
	) -> Result<(BlockImportParams<B>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		let inherent_data = self.inherent_data_providers
			.create_inherent_data().map_err(String::from)?;
		let timestamp_now = inherent_data.timestamp_inherent_data().map_err(String::from)?;

		let best_hash = self.client.info().best_hash;
		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		let parent_aux_key = POW_AUX_PREFIX.iter().chain(&parent_hash[..])
			.cloned().collect::<Vec<_>>();
		let best_aux_key = POW_AUX_PREFIX.iter().chain(&best_hash[..])
			.cloned().collect::<Vec<_>>();
		let best_aux = match self.client.get_aux(&best_aux_key)
			.map_err(|e| format!("{:?}", e))?
		{
			Some(bytes) => PowAux::decode(&mut &bytes[..]).map_err(|e| format!("{:?}", e))?,
			None => Default::default(),
		};
		let mut aux = match self.client.get_aux(&parent_aux_key)
			.map_err(|e| format!("{:?}", e))?
		{
			Some(bytes) => PowAux::decode(&mut &bytes[..]).map_err(|e| format!("{:?}", e))?,
			None => Default::default(),
		};

		let (checked_header, difficulty, seal) = self.check_header::<B>(
			header,
			BlockId::Hash(parent_hash),
		)?;
		aux.total_difficulty += difficulty;

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
			auxiliary: vec![(POW_AUX_PREFIX.iter().chain(&hash[..]).cloned().collect::<Vec<_>>(),
							 Some(aux.encode()))],
			fork_choice: ForkChoiceStrategy::Custom(aux.total_difficulty > best_aux.total_difficulty),
		};

		Ok((import_block, None))
	}
}

/// The PoW import queue type.
pub type PowImportQueue<B> = BasicQueue<B>;

pub fn import_queue<B, C>(
	block_import: BoxBlockImport<B>,
	client: Arc<C>,
	inherent_data_providers: InherentDataProviders,
) -> Result<PowImportQueue<B>, consensus_common::Error> where
	B: BlockT<Hash=H256>,
	C: 'static + ProvideRuntimeApi + HeaderBackend<B> + BlockOf + ProvideCache<B> + Send + Sync + AuxStore,
	C::Api: BlockBuilderApi<B> + PowApi<B>,
{
	if !inherent_data_providers.has_provider(&srml_timestamp::INHERENT_IDENTIFIER) {
		match inherent_data_providers.register_provider(srml_timestamp::InherentDataProvider) {
			Ok(()) => (),
			Err(e) => warn!("Registering inherent data provider for timestamp failed"),
		}
	}

	let verifier = PowVerifier {
		client: client.clone(),
		inherent_data_providers,
	};

	Ok(BasicQueue::new(
		verifier,
		block_import,
		None,
		None
	))
}

pub fn start_mine<B: BlockT<Hash=H256>, I, C, E>(
	block_import: Arc<Mutex<I>>,
	client: Arc<C>,
	mut env: E,
	inherent_data_providers: inherents::InherentDataProviders,
) where
	I: BlockImport<B> + Send + Sync + 'static,
	C: HeaderBackend<B> + AuxStore + ProvideRuntimeApi + 'static,
	C::Api: PowApi<B>,
	E: Environment<B> + Send + Sync + 'static,
	E::Error: core::fmt::Debug,
{
	if !inherent_data_providers.has_provider(&srml_timestamp::INHERENT_IDENTIFIER) {
		match inherent_data_providers.register_provider(srml_timestamp::InherentDataProvider) {
			Ok(()) => (),
			Err(e) => warn!("Registering inherent data provider for timestamp failed"),
		}
	}

	thread::spawn(move || {
		loop {
			match mine_one(&block_import, &client, &mut env, &inherent_data_providers) {
				Ok(()) => (),
				Err(e) => warn!("Mining block failed: {:?}", e),
			}

			std::thread::sleep(std::time::Duration::new(1, 0));
		}
	});
}

pub fn mine_one<B: BlockT<Hash=H256>, I, C, E>(
	block_import: &Arc<Mutex<I>>,
	client: &Arc<C>,
	env: &mut E,
	inherent_data_providers: &inherents::InherentDataProviders,
) -> Result<(), String> where
	I: BlockImport<B>,
	C: HeaderBackend<B> + AuxStore + ProvideRuntimeApi,
	C::Api: PowApi<B>,
	E: Environment<B>,
	E::Error: core::fmt::Debug,
{
	let best_hash = client.info().best_hash;
	let best_header = client.header(BlockId::Hash(best_hash))
		.map_err(|e| format!("Best header does not exist: {:?}", e))?
		.ok_or("Fetching best header failed")?;
	let best_aux_key = POW_AUX_PREFIX.iter().chain(&best_hash[..])
		.cloned().collect::<Vec<_>>();
	let mut aux = match client.get_aux(&best_aux_key)
		.map_err(|e| format!("{:?}", e))?
	{
		Some(bytes) => PowAux::decode(&mut &bytes[..]).map_err(|e| format!("{:?}", e))?,
		None => Default::default(),
	};
	let mut proposer = env.init(&best_header).map_err(|e| format!("{:?}", e))?;

	let inherent_data = inherent_data_providers
		.create_inherent_data().map_err(String::from)?;
	let block = futures::executor::block_on(proposer.propose(
		inherent_data,
		Default::default(),
		std::time::Duration::new(1, 0)
	)).map_err(|e| format!("Block proposing error: {:?}", e))?;

	let (mut header, body) = block.deconstruct();
	let (difficulty, seal) = client.runtime_api().mine(
		&BlockId::Hash(best_hash),
		&header.hash(),
	).map_err(|e| format!("Mine sealing runtime error: {:?}", e))?;

	aux.total_difficulty += difficulty;
	let hash = header.hash();

	let import_block = BlockImportParams {
		origin: BlockOrigin::Own,
		header,
		justification: None,
		post_digests: vec![DigestItem::Seal(POW_ENGINE_ID, seal)],
		body: Some(body),
		finalized: false,
		auxiliary: vec![(POW_AUX_PREFIX.iter().chain(&hash[..]).cloned().collect::<Vec<_>>(),
						 Some(aux.encode()))],
		fork_choice: ForkChoiceStrategy::Custom(true),
	};

	if let Err(err) = block_import.lock().expect("Lock failed").import_block(import_block, Default::default()) {
		warn!("Error with block built on {:?}: {:?}",
			  best_hash,
			  err,
		);
	}
	Ok(())
}
