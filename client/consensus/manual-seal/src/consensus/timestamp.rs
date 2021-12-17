use crate::Error;
use sc_client_api::{AuxStore, UsageProvider};
use sc_consensus_aura::slot_duration;
use sc_consensus_babe::Config;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_consensus_aura::{
	sr25519::{AuthorityId, AuthoritySignature},
	AuraApi,
};
use sp_consensus_babe::BabeApi;
use sp_inherents::{InherentData, InherentDataProvider, InherentIdentifier};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, Zero},
};
use sp_timestamp::{InherentType, INHERENT_IDENTIFIER};
use std::{
	sync::{atomic, Arc},
	time::SystemTime,
};

/// Provide duration since unix epoch in millisecond for timestamp inherent.
/// Mocks the timestamp inherent to always produce the timestamp for the next babe slot.
pub struct SlotTimestampProvider {
	time: atomic::AtomicU64,
	slot_duration: u64,
}

impl SlotTimestampProvider {
	/// Create a new mocked time stamp provider, for babe
	pub fn babe<B, C>(client: Arc<C>) -> Result<Self, Error>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: BabeApi<B>,
	{
		let slot_duration = Config::get_or_compute(&*client)?.slot_duration;
		let info = client.info();

		// looks like this isn't the first block, rehydrate the fake time.
		// otherwise we'd be producing blocks for older slots.
		let time = if info.best_number != Zero::zero() {
			let header = client.header(BlockId::Hash(info.best_hash))?.unwrap();
			let slot = sc_consensus_babe::find_pre_digest::<B>(&header).unwrap().slot();
			// add the slot duration so there's no collision of slots
			(*slot * slot_duration) + slot_duration
		} else {
			// this is the first block, use the correct time.
			let now = SystemTime::now();
			now.duration_since(SystemTime::UNIX_EPOCH)
				.map_err(|err| Error::StringError(format!("{}", err)))?
				.as_millis() as u64
		};

		Ok(Self { time: atomic::AtomicU64::new(time), slot_duration })
	}

	/// Create a new mocked time stamp provider, for aura
	pub fn aura<B, C>(client: Arc<C>) -> Result<Self, Error>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: AuraApi<B, AuthorityId>,
	{
		let slot_duration = (*slot_duration(&*client)?).get();
		let info = client.info();

		// looks like this isn't the first block, rehydrate the fake time.
		// otherwise we'd be producing blocks for older slots.
		let time = if info.best_number != Zero::zero() {
			let header = client.header(BlockId::Hash(info.best_hash))?.unwrap();
			let slot =
				sc_consensus_aura::find_pre_digest::<B, AuthoritySignature>(&header).unwrap();
			// add the slot duration so there's no collision of slots
			(*slot * slot_duration) + slot_duration
		} else {
			// this is the first block, use the correct time.
			let now = SystemTime::now();
			now.duration_since(SystemTime::UNIX_EPOCH)
				.map_err(|err| Error::StringError(format!("{}", err)))?
				.as_millis() as u64
		};

		Ok(Self { time: atomic::AtomicU64::new(time), slot_duration })
	}

	/// Get the current slot number
	pub fn slot(&self) -> u64 {
		self.time.load(atomic::Ordering::SeqCst) / self.slot_duration
	}

	/// Gets the current time stamp.
	pub fn timestamp(&self) -> sp_timestamp::Timestamp {
		sp_timestamp::Timestamp::new(self.time.load(atomic::Ordering::SeqCst))
	}
}

#[async_trait::async_trait]
impl InherentDataProvider for SlotTimestampProvider {
	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), sp_inherents::Error> {
		// we update the time here.
		let new_time: InherentType =
			self.time.fetch_add(self.slot_duration, atomic::Ordering::SeqCst).into();
		inherent_data.put_data(INHERENT_IDENTIFIER, &new_time)?;
		Ok(())
	}

	async fn try_handle_error(
		&self,
		_: &InherentIdentifier,
		_: &[u8],
	) -> Option<Result<(), sp_inherents::Error>> {
		None
	}
}
