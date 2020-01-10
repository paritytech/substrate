use std::{sync::Arc, marker::PhantomData, time::{Duration, Instant}};
use log::trace;
use parking_lot::Mutex;
use sp_core::{Blake2Hasher, H256};
use sp_blockchain::{Result as ClientResult, ProvideCache, HeaderMetadata};
use sp_inherents::InherentData;
use sp_timestamp::{TimestampInherentData, InherentType as TimestampInherent};
use sp_consensus::{Error as ConsensusError, BlockImportParams, BlockOrigin};
use sp_consensus::import_queue::{Verifier, CacheKeyId, BasicQueue};
use sp_consensus_sassafras::digest::{NextEpochDescriptor, PostBlockDescriptor, PreDigest};
use sp_consensus_sassafras::inherents::SassafrasInherentData;
use sp_runtime::{generic::BlockId, Justification};
use sp_runtime::traits::{Block as BlockT, Header, ProvideRuntimeApi};
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sc_client::{Client, CallExecutor};
use sc_client_api::backend::{AuxStore, Backend};
use sc_consensus_slots::SlotCompatible;

mod aux_schema;

#[derive(derive_more::Display, Debug)]
enum Error<B: BlockT> {
	#[display(fmt = "Could not extract timestamp and slot: {:?}", _0)]
	Extraction(sp_consensus::Error),
	#[display(fmt = "Header {:?} rejected: too far in the future", _0)]
	TooFarInFuture(B::Hash),
	#[display(fmt = "Parent ({}) of {} unavailable. Cannot import", _0, _1)]
	ParentUnavailable(B::Hash, B::Hash),
	#[display(fmt = "Could not fetch parent header: {:?}", _0)]
	FetchParentHeader(sp_blockchain::Error),
	Runtime(sp_inherents::Error),
	Client(sp_blockchain::Error),
}

impl<B: BlockT> std::convert::From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

pub struct SassafrasVerifier<B, E, Block: BlockT, RA, PRA> {
	client: Arc<Client<B, E, Block, RA>>,
	api: Arc<PRA>,
	inherent_data_providers: sp_inherents::InherentDataProviders,
	time_source: TimeSource,
}

impl<B, E, Block, RA, PRA> Verifier<Block> for SassafrasVerifier<B, E, Block, RA, PRA> where
	Block: BlockT<Hash=H256>,
	B: Backend<Block, Blake2Hasher> + 'static,
	E: CallExecutor<Block, Blake2Hasher> + 'static + Clone + Send + Sync,
	RA: Send + Sync,
	PRA: ProvideRuntimeApi + Send + Sync + AuxStore + ProvideCache<Block>,
	PRA::Api: BlockBuilderApi<Block, Error = sp_blockchain::Error>,
{
	fn verify(
		&mut self,
		origin: BlockOrigin,
		header: Block::Header,
		justification: Option<Justification>,
		mut body: Option<Vec<Block::Extrinsic>>,
	) -> Result<(BlockImportParams<Block>, Option<Vec<(CacheKeyId, Vec<u8>)>>), String> {
		trace!(
			target: "sassafras",
			"Verifying origin: {:?} header: {:?} justification: {:?} body: {:?}",
			origin,
			header,
			justification,
			body,
		);

		let mut inherent_data = self
			.inherent_data_providers
			.create_inherent_data()
			.map_err(Error::<Block>::Runtime)?;

		let (_, slot_now, _) = self.time_source.extract_timestamp_and_slot(&inherent_data)
			.map_err(Error::<Block>::Extraction)?;

		let hash = header.hash();
		let parent_hash = *header.parent_hash();
		let mut auxiliary = aux_schema::load_auxiliary(&parent_hash, self.api.as_ref())
			.map_err(Error::<Block>::Client)?;

		let parent_header_metadata = self.client.header_metadata(parent_hash)
			.map_err(Error::<Block>::FetchParentHeader)?;

		let pre_digest = find_pre_digest::<Block>(&header)?;
		let post_block_desc = find_post_block_descriptor::<Block>(&header)?;

		// TODO: verify ticket VRF and post VRF.
		// TODO: verify that auxiliary.validating is the ticket VRF.

		// auxiliary.publishing.push(post_digests.commitments);

		if let Some(next_epoch_desc) = find_next_epoch_descriptor::<Block>(&header)? {
			unimplemented!()
		}

		unimplemented!()
	}
}

pub type SassafrasImportQueue<B> = BasicQueue<B>;

#[derive(Default, Clone)]
struct TimeSource(Arc<Mutex<(Option<Duration>, Vec<(Instant, u64)>)>>);

impl SlotCompatible for TimeSource {
	fn extract_timestamp_and_slot(
		&self,
		data: &InherentData,
	) -> Result<(TimestampInherent, u64, std::time::Duration), sp_consensus::Error> {
		trace!(target: "babe", "extract timestamp");
		data.timestamp_inherent_data()
			.and_then(|t| data.sassafras_inherent_data().map(|a| (t, a)))
			.map_err(Into::into)
			.map_err(sp_consensus::Error::InherentData)
			.map(|(x, y)| (x, y, self.0.lock().0.take().unwrap_or_default()))
	}
}

fn find_pre_digest<B: BlockT>(
	header: &B::Header,
) -> Result<PreDigest, Error<B>> {
	unimplemented!()
}

fn find_post_block_descriptor<B: BlockT>(
	header: &B::Header,
) -> Result<Option<PostBlockDescriptor>, Error<B>> {
	unimplemented!()
}

fn find_next_epoch_descriptor<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextEpochDescriptor>, Error<B>> {
	unimplemented!()
}
