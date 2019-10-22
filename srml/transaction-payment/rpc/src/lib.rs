// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! RPC interface for the t
//! ransa
//!ction payment module.
use std::sync::Arc;
use serde::{Serialize, Deserialize};
use codec::Codec;
use client::blockchain::HeaderBackend;
use jsonrpc_core::{Error, ErrorCode, Result};
use jsonrpc_derive::rpc;
use sr_primitives::{
	generic::BlockId,
	traits::{Block as BlockT, ProvideRuntimeApi},
};
use srml_transaction_payment_rpc_runtime_api::{
	TransactionPaymentApi as TransactionPaymentRuntimeApi, RuntimeDispatchInfo,
};
use self::gen_client::Client as TransactionPaymentClient;


/// A wrapper around the request information to query a dispatchable info.
#[derive(Serialize, Deserialize)]
pub struct DispatchInfoRequest<AccountId, Extra, Call> {
	/// Sender aka. origin of the dispatch.
	pub origin: AccountId,
	/// The call type.
	pub call: Call,
	/// Signed extensions.
	pub extra: Extra,
}

#[rpc]
pub trait TransactionPaymentApi<BlockHash, AccountId, Balance, Call, Extra> {
	#[rpc(name = "transaction_payment_query_unsigned")]
	fn query_info_unsigned(
		&self,
		request: DispatchInfoRequest<AccountId, Extra, Call>
	) -> Result<RuntimeDispatchInfo<Balance>>;
}

/// A struct that implements the [`TransactionPaymentApi`].
pub struct TransactionPayment<C, B> {
	client: Arc<C>,
	_marker: std::marker::PhantomData<B>,
}

impl<C, B> TransactionPayment<C, B> {
	pub fn new(client: Arc<C>) -> Self {
		TransactionPayment { client, _marker: Default::default() }
	}
}

impl<
	C,
	Block,
	AccountId,
	Balance,
	Call,
	Extra,
> TransactionPaymentApi<
	<Block as BlockT>::Hash,
	AccountId,
	Balance,
	Call,
	Extra,
> for TransactionPayment<C, Block> where
	Block: BlockT,
	C: Send + Sync + 'static + ProvideRuntimeApi + HeaderBackend<Block>,
	C::Api: TransactionPaymentRuntimeApi<Block, AccountId, Balance, Call, Extra>,
	AccountId: Codec,
	Balance: Codec,
	Call: Codec,
	Extra: Codec,
{
	fn query_info_unsigned(
		&self,
		request: DispatchInfoRequest<AccountId, Extra, Call>
	) -> Result<RuntimeDispatchInfo<Balance>> {
		let api = self.client.runtime_api();
		let best = self.client.info().best_hash;
		let at = BlockId::hash(best);

		let DispatchInfoRequest { origin, extra, call } = request;
		api.query_info_unsigned(&at, origin, call, extra).map_err(|e| Error {
			code: ErrorCode::ServerError(1),
			message: "Unable to query dispatch info.".into(),
			data: Some(format!("{:?}", e).into()),
		})
	}
}
