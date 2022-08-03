// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! RPC interface for the transaction payment pallet.

use std::{convert::TryInto, sync::Arc};

use codec::{Codec, Decode};
use jsonrpsee::{
	core::{async_trait, Error as JsonRpseeError, RpcResult},
	proc_macros::rpc,
	types::error::{CallError, ErrorCode, ErrorObject},
};
use pallet_vesting_mangata_rpc_runtime_api::{VestingInfosWithLockedAt};
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::Bytes;
use sp_rpc::number::NumberOrHex;
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, MaybeDisplay, MaybeFromStr},
};

pub use pallet_vesting_mangata_rpc_runtime_api::VestingMangataApi as VestingMangataRuntimeApi;

#[rpc(client, server)]
pub trait VestingMangataApi<BlockHash, AccountId, TokenId, Balance, BlockNumber, ResponseTypeVestingInfosWithLockedAt> {
	#[method(name = "vesting_getVestingLockedAt")]
	fn get_vesting_locked_at(&self, who: AccountId, token_id: TokenId, at_block_number: Option<BlockNumber>, at: Option<BlockHash>) -> RpcResult<ResponseTypeVestingInfosWithLockedAt>;
}

/// Provides RPC methods to query a dispatchable's class, weight and fee.
pub struct VestingMangata<C, P> {
	/// Shared reference to the client.
	client: Arc<C>,
	_marker: std::marker::PhantomData<P>,
}

impl<C, P> VestingMangata<C, P> {
	/// Creates a new instance of the TransactionPayment Rpc helper.
	pub fn new(client: Arc<C>) -> Self {
		Self { client, _marker: Default::default() }
	}
}

#[async_trait]
impl<C, Block, Balance, TokenId, AccountId, BlockNumber>
	VestingMangataApiServer<
		<Block as BlockT>::Hash,
		AccountId,
		TokenId,
		Balance,
		BlockNumber,
		VestingInfosWithLockedAt<Balance, BlockNumber>>
	for VestingMangata<C, Block>
where
	Block: BlockT,
	C: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	C::Api: VestingMangataRuntimeApi<Block, AccountId, TokenId, Balance, BlockNumber>,
	Balance: Codec + MaybeDisplay + MaybeFromStr + sp_std::fmt::Debug,
	TokenId: Codec + MaybeDisplay + MaybeFromStr + sp_std::fmt::Debug,
	BlockNumber: Codec + MaybeDisplay + MaybeFromStr + sp_std::fmt::Debug,
	AccountId: Codec + MaybeDisplay + MaybeFromStr + sp_std::fmt::Debug,
{
	fn get_vesting_locked_at(&self, who: AccountId, token_id: TokenId, at_block_number: Option<BlockNumber>, at: Option<<Block as BlockT>::Hash>)
	 -> RpcResult<VestingInfosWithLockedAt<Balance, BlockNumber>> {
		let api = self.client.runtime_api();
		let at = BlockId::<Block>::hash(at.unwrap_or_else(||
            // If the block hash is not supplied assume the best block.
            self.client.info().best_hash));

		let runtime_api_result = api.get_vesting_locked_at(
			&at,
			who,
			token_id,
			at_block_number,
		);
		runtime_api_result.map_err(|e| {
			JsonRpseeError::Call(CallError::Custom(ErrorObject::owned(
				1,
				"Unable to serve the request",
				Some(format!("{:?}", e)),
			)))
		})
	}
}
