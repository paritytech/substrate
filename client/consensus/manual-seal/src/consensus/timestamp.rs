// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Mocked timestamp inherent, allows for manual seal to create blocks for runtimes
//! that expect this inherent.

use crate::Error;
use sc_client_api::{AuxStore, UsageProvider};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_consensus_aura::{
	sr25519::{AuthorityId, AuthoritySignature},
	AuraApi,
};
use sp_consensus_babe::BabeApi;
use sp_consensus_slots::{Slot, SlotDuration};
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
/// Mocks the timestamp inherent to always produce a valid timestamp for the next slot.
///
/// This works by either fetching the `slot_number` from the most recent header and dividing
/// that value by `slot_duration` in order to fork chains that expect this inherent.
///
/// It produces timestamp inherents that are increased by `slot_duration` whenever
/// `provide_inherent_data` is called.
pub struct SlotTimestampProvider {
	// holds the unix millisecond timestamp for the most recent block
	unix_millis: atomic::AtomicU64,
	// configured slot_duration in the runtime
	slot_duration: SlotDuration,
}

impl SlotTimestampProvider {
	/// Create a new mocked time stamp provider, for babe.
	pub fn new_babe<B, C>(client: Arc<C>) -> Result<Self, Error>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: BabeApi<B>,
	{
		let slot_duration = sc_consensus_babe::configuration(&*client)?.slot_duration();

		let time = Self::with_header(&client, slot_duration, |header| {
			let slot_number = *sc_consensus_babe::find_pre_digest::<B>(&header)
				.map_err(|err| format!("{}", err))?
				.slot();
			Ok(slot_number)
		})?;

		Ok(Self { unix_millis: atomic::AtomicU64::new(time), slot_duration })
	}

	/// Create a new mocked time stamp provider, for aura
	pub fn new_aura<B, C>(client: Arc<C>) -> Result<Self, Error>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + ProvideRuntimeApi<B> + UsageProvider<B>,
		C::Api: AuraApi<B, AuthorityId>,
	{
		let slot_duration = sc_consensus_aura::slot_duration(&*client)?;

		let time = Self::with_header(&client, slot_duration, |header| {
			let slot_number = *sc_consensus_aura::find_pre_digest::<B, AuthoritySignature>(&header)
				.map_err(|err| format!("{}", err))?;
			Ok(slot_number)
		})?;

		Ok(Self { unix_millis: atomic::AtomicU64::new(time), slot_duration })
	}

	fn with_header<F, C, B>(
		client: &Arc<C>,
		slot_duration: SlotDuration,
		func: F,
	) -> Result<u64, Error>
	where
		B: BlockT,
		C: AuxStore + HeaderBackend<B> + UsageProvider<B>,
		F: Fn(B::Header) -> Result<u64, Error>,
	{
		let info = client.info();

		// looks like this isn't the first block, rehydrate the fake time.
		// otherwise we'd be producing blocks for older slots.
		let time = if info.best_number != Zero::zero() {
			let header = client
				.header(BlockId::Hash(info.best_hash))?
				.ok_or_else(|| "best header not found in the db!".to_string())?;
			let slot = func(header)?;
			// add the slot duration so there's no collision of slots
			(slot * slot_duration.as_millis() as u64) + slot_duration.as_millis() as u64
		} else {
			// this is the first block, use the correct time.
			let now = SystemTime::now();
			now.duration_since(SystemTime::UNIX_EPOCH)
				.map_err(|err| Error::StringError(format!("{}", err)))?
				.as_millis() as u64
		};

		Ok(time)
	}

	/// Get the current slot number
	pub fn slot(&self) -> Slot {
		Slot::from_timestamp(
			self.unix_millis.load(atomic::Ordering::SeqCst).into(),
			self.slot_duration,
		)
	}

	/// Gets the current time stamp.
	pub fn timestamp(&self) -> sp_timestamp::Timestamp {
		sp_timestamp::Timestamp::new(self.unix_millis.load(atomic::Ordering::SeqCst))
	}
}

#[async_trait::async_trait]
impl InherentDataProvider for SlotTimestampProvider {
	async fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> Result<(), sp_inherents::Error> {
		// we update the time here.
		let new_time: InherentType = self
			.unix_millis
			.fetch_add(self.slot_duration.as_millis() as u64, atomic::Ordering::SeqCst)
			.into();
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
