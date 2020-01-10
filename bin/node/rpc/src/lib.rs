// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! A collection of node-specific RPC methods.
//!
//! Since `substrate` core functionality makes no assumptions
//! about the modules used inside the runtime, so do
//! RPC methods defined in `sc-rpc` crate.
//! It means that `client/rpc` can't have any methods that
//! need some strong assumptions about the particular runtime.
//!
//! The RPCs available in this crate however can make some assumptions
//! about how the runtime is constructed and what `SRML` modules
//! are part of it. Therefore all node-runtime-specific RPCs can
//! be placed here or imported from corresponding `SRML` RPC definitions.

#![warn(missing_docs)]

use std::sync::Arc;

use node_primitives::{Block, AccountId, Index, Balance};
use node_runtime::UncheckedExtrinsic;
use sp_api::ProvideRuntimeApi;
use sp_transaction_pool::TransactionPool;

/// Light client extra dependencies.
pub struct LightDeps<F> {
	/// Remote access to the blockchain (async).
	pub remote_blockchain: Arc<dyn sc_client::light::blockchain::RemoteBlockchain<Block>>,
	/// Fetcher instance.
	pub fetcher: Arc<F>,
}

impl<F> LightDeps<F> {
	/// Create empty `LightDeps` with given `F` type.
	///
	/// This is a convenience method to be used in the service builder,
	/// to make sure the type of the `LightDeps<F>` is matching.
	pub fn none(_: Option<Arc<F>>) -> Option<Self> {
		None
	}
}

/// Instantiate all RPC extensions.
///
/// If you provide `LightDeps`, the system is configured for light client.
pub fn create<C, P, M, F>(
	client: Arc<C>,
	pool: Arc<P>,
	light_deps: Option<LightDeps<F>>,
) -> jsonrpc_core::IoHandler<M> where
	C: ProvideRuntimeApi<Block>,
	C: sc_client::blockchain::HeaderBackend<Block>,
	C: Send + Sync + 'static,
	C::Api: substrate_frame_rpc_system::AccountNonceApi<Block, AccountId, Index>,
	C::Api: pallet_contracts_rpc::ContractsRuntimeApi<Block, AccountId, Balance>,
	C::Api: pallet_transaction_payment_rpc::TransactionPaymentRuntimeApi<Block, Balance, UncheckedExtrinsic>,
	F: sc_client::light::fetcher::Fetcher<Block> + 'static,
	P: TransactionPool + 'static,
	M: jsonrpc_core::Metadata + Default,
{
	use substrate_frame_rpc_system::{FullSystem, LightSystem, SystemApi};
	use pallet_contracts_rpc::{Contracts, ContractsApi};
	use pallet_transaction_payment_rpc::{TransactionPayment, TransactionPaymentApi};

	let mut io = jsonrpc_core::IoHandler::default();

	if let Some(LightDeps { remote_blockchain, fetcher }) = light_deps {
		io.extend_with(
			SystemApi::<AccountId, Index>::to_delegate(LightSystem::new(client, remote_blockchain, fetcher, pool))
		);
	} else {
		io.extend_with(
			SystemApi::to_delegate(FullSystem::new(client.clone(), pool))
		);

		// Making synchronous calls in light client freezes the browser currently,
		// more context: https://github.com/paritytech/substrate/pull/3480
		// These RPCs should use an asynchronous caller instead.
		io.extend_with(
			ContractsApi::to_delegate(Contracts::new(client.clone()))
		);
		io.extend_with(
			TransactionPaymentApi::to_delegate(TransactionPayment::new(client))
		);
	}
	io
}
