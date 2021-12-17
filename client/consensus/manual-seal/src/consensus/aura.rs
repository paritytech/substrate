use crate::{ConsensusDataProvider, Error};
use sc_client_api::{AuxStore, UsageProvider};
use sc_consensus::BlockImportParams;
use sc_consensus_aura::slot_duration;
use sp_api::{ProvideRuntimeApi, TransactionFor};
use sp_blockchain::{HeaderBackend, HeaderMetadata};
use sp_consensus_aura::{
	digests::CompatibleDigestItem,
	sr25519::{AuthorityId, AuthoritySignature},
	AuraApi,
};
use sp_inherents::InherentData;
use sp_runtime::{traits::Block as BlockT, Digest, DigestItem};
use sp_timestamp::TimestampInherentData;
use std::{marker::PhantomData, sync::Arc};

/// Consensus data provider for Aura
pub struct AuraConsensusDataProvider<B, C> {
	_client: Arc<C>,

	slot_duration: u64,

	_phantom: PhantomData<B>,
}

impl<B, C> AuraConsensusDataProvider<B, C>
where
	B: BlockT,
	C: AuxStore + ProvideRuntimeApi<B> + UsageProvider<B>,
	C::Api: AuraApi<B, AuthorityId>,
{
	pub fn new(client: Arc<C>) -> Self {
		let slot_duration =
			(*slot_duration(&*client).expect("slot_duration is always present; qed.")).get();

		Self { _client: client, slot_duration, _phantom: PhantomData }
	}
}

impl<B, C> ConsensusDataProvider<B> for AuraConsensusDataProvider<B, C>
where
	B: BlockT,
	C: AuxStore
		+ HeaderBackend<B>
		+ HeaderMetadata<B, Error = sp_blockchain::Error>
		+ UsageProvider<B>
		+ ProvideRuntimeApi<B>,
	C::Api: AuraApi<B, AuthorityId>,
{
	type Transaction = TransactionFor<C, B>;

	fn create_digest(
		&self,
		_parent: &B::Header,
		_inherents: &InherentData,
	) -> Result<Digest, Error> {
		let time_stamp =
			*_inherents.timestamp_inherent_data()?.expect("Timestamp is always present; qed");
		let item = <DigestItem as CompatibleDigestItem<AuthoritySignature>>::aura_pre_digest(
			(time_stamp / self.slot_duration).into(),
		);
		Ok(Digest { logs: vec![item] })
	}

	fn append_block_import(
		&self,
		_parent: &B::Header,
		_params: &mut BlockImportParams<B, Self::Transaction>,
		_inherents: &InherentData,
	) -> Result<(), Error> {
		Ok(())
	}
}
