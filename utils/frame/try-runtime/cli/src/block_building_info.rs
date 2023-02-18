// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::BlockT;
use parity_scale_codec::Encode;
use sc_cli::Result;
use sp_consensus_aura::{Slot, SlotDuration, AURA_ENGINE_ID};
use sp_consensus_babe::{
	digests::{PreDigest, SecondaryPlainPreDigest},
	BABE_ENGINE_ID,
};
use sp_inherents::{InherentData, InherentDataProvider};
use sp_runtime::{Digest, DigestItem};
use sp_timestamp::TimestampInherentData;

/// Something that can create inherent data providers and pre-runtime digest.
///
/// It is possible for the caller to provide custom arguments to the callee by setting the
/// `ExtraArgs` generic parameter.
///
/// This module already provides some convenience implementation of this trait for closures. So, it
/// should not be required to implement it directly.
#[async_trait::async_trait]
pub trait BlockBuildingInfoProvider<Block: BlockT, ExtraArgs = ()> {
	type InherentDataProviders: InherentDataProvider;

	async fn get_inherent_providers_and_pre_digest(
		&self,
		parent_hash: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<(Self::InherentDataProviders, Vec<DigestItem>)>;
}

#[async_trait::async_trait]
impl<F, Block, IDP, ExtraArgs, Fut> BlockBuildingInfoProvider<Block, ExtraArgs> for F
where
	Block: BlockT,
	F: Fn(Block::Hash, ExtraArgs) -> Fut + Sync + Send,
	Fut: std::future::Future<Output = Result<(IDP, Vec<DigestItem>)>> + Send + 'static,
	IDP: InherentDataProvider + 'static,
	ExtraArgs: Send + 'static,
{
	type InherentDataProviders = IDP;

	async fn get_inherent_providers_and_pre_digest(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<(Self::InherentDataProviders, Vec<DigestItem>)> {
		(*self)(parent, extra_args).await
	}
}

/// Provides [`BlockBuildingInfoProvider`] implementation for chains that include timestamp inherent
/// and use Aura for a block production.
///
/// It depends only on the expected block production frequency, i.e. `blocktime_millis`.
pub fn timestamp_with_aura_info<Block: BlockT>(
	blocktime_millis: u64,
) -> impl BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>> {
	move |_, maybe_prev_info: Option<(InherentData, Digest)>| async move {
		let timestamp_idp = match maybe_prev_info {
			Some((inherent_data, _)) => sp_timestamp::InherentDataProvider::new(
				inherent_data.timestamp_inherent_data().unwrap().unwrap() + blocktime_millis,
			),
			None => sp_timestamp::InherentDataProvider::from_system_time(),
		};

		let slot =
			Slot::from_timestamp(*timestamp_idp, SlotDuration::from_millis(blocktime_millis));
		let digest = vec![DigestItem::PreRuntime(AURA_ENGINE_ID, slot.encode())];

		Ok((timestamp_idp, digest))
	}
}

/// Provides [`BlockBuildingInfoProvider`] implementation for chains that include timestamp inherent
/// and use Babe for a block production.
///
/// It depends only on the expected block production frequency, i.e. `blocktime_millis`.
pub fn timestamp_with_babe_info<Block: BlockT>(
	blocktime_millis: u64,
) -> impl BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>> {
	move |_, maybe_prev_info: Option<(InherentData, Digest)>| async move {
		let timestamp_idp = match maybe_prev_info {
			Some((inherent_data, _)) => sp_timestamp::InherentDataProvider::new(
				inherent_data.timestamp_inherent_data().unwrap().unwrap() + blocktime_millis,
			),
			None => sp_timestamp::InherentDataProvider::from_system_time(),
		};

		let slot =
			Slot::from_timestamp(*timestamp_idp, SlotDuration::from_millis(blocktime_millis));
		let slot_idp = sp_consensus_babe::inherents::InherentDataProvider::new(slot);

		let digest = vec![DigestItem::PreRuntime(
			BABE_ENGINE_ID,
			PreDigest::SecondaryPlain(SecondaryPlainPreDigest { slot, authority_index: 0 })
				.encode(),
		)];

		Ok(((slot_idp, timestamp_idp), digest))
	}
}

/// Provides [`BlockBuildingInfoProvider`] implementation for chains that use:
///  - timestamp inherent,
///  - Babe for a block production (inherent + digest),
///  - uncles inherent,
///  - storage proof inherent
///
/// It depends only on the expected block production frequency, i.e. `blocktime_millis`.
pub fn substrate_info<Block: BlockT>(
	blocktime_millis: u64,
) -> impl BlockBuildingInfoProvider<Block, Option<(InherentData, Digest)>> {
	move |_, maybe_prev_info: Option<(InherentData, Digest)>| async move {
		let timestamp_idp = match maybe_prev_info {
			Some((inherent_data, _)) => sp_timestamp::InherentDataProvider::new(
				inherent_data.timestamp_inherent_data().unwrap().unwrap() + blocktime_millis,
			),
			None => sp_timestamp::InherentDataProvider::from_system_time(),
		};

		let slot =
			Slot::from_timestamp(*timestamp_idp, SlotDuration::from_millis(blocktime_millis));
		let slot_idp = sp_consensus_babe::inherents::InherentDataProvider::new(slot);

		let storage_proof_idp = sp_transaction_storage_proof::InherentDataProvider::new(None);

		let digest = vec![DigestItem::PreRuntime(
			BABE_ENGINE_ID,
			PreDigest::SecondaryPlain(SecondaryPlainPreDigest { slot, authority_index: 0 })
				.encode(),
		)];

		Ok(((slot_idp, timestamp_idp, storage_proof_idp), digest))
	}
}
