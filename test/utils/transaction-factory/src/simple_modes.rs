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

/// This module implements two manufacturing modes:
///
/// # MasterToN
/// Manufacture `num` transactions from the master account
/// to `num` randomly created accounts, one each.
///
///   A -> B
///   A -> C
///   ... x `num`
///
///
/// # MasterTo1
/// Manufacture `num` transactions from the master account
/// to exactly one other randomly created account.
///
///   A -> B
///   A -> B
///   ... x `num`

use std::sync::Arc;

use log::info;
use client::Client;
use block_builder_api::BlockBuilder;
use sp_api::ConstructRuntimeApi;
use primitives::{Blake2Hasher, Hasher};
use sp_runtime::traits::{Block as BlockT, ProvideRuntimeApi, One};
use sp_runtime::generic::BlockId;

use crate::{Mode, RuntimeAdapter, create_block};

pub fn next<RA, Backend, Exec, Block, RtApi>(
	factory_state: &mut RA,
	client: &Arc<Client<Backend, Exec, Block, RtApi>>,
	version: u32,
	genesis_hash: <RA::Block as BlockT>::Hash,
	prior_block_hash: <RA::Block as BlockT>::Hash,
	prior_block_id: BlockId<Block>,
) -> Option<Block>
where
	Block: BlockT<Hash = <Blake2Hasher as Hasher>::Out>,
	Exec: client::CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone,
	Backend: client_api::backend::Backend<Block, Blake2Hasher> + Send,
	Client<Backend, Exec, Block, RtApi>: ProvideRuntimeApi,
	<Client<Backend, Exec, Block, RtApi> as ProvideRuntimeApi>::Api:
		BlockBuilder<Block, Error = sp_blockchain::Error>,
	RtApi: ConstructRuntimeApi<Block, Client<Backend, Exec, Block, RtApi>> + Send + Sync,
	RA: RuntimeAdapter,
{
	if factory_state.block_no() >= factory_state.num() {
		return None;
	}

	let from = (RA::master_account_id(), RA::master_account_secret());

	let seed = match factory_state.mode() {
		// choose the same receiver for all transactions
		Mode::MasterTo1 => factory_state.start_number(),

		// different receiver for each transaction
		Mode::MasterToN => factory_state.start_number() + factory_state.block_no(),
		_ => unreachable!("Mode not covered!"),
	};
	let to = RA::gen_random_account_id(&seed);

	let amount = RA::minimum_balance();

	let transfer = factory_state.transfer_extrinsic(
		&from.0,
		&from.1,
		&to,
		&amount,
		version,
		&genesis_hash,
		&prior_block_hash,
	);

	let inherents = RA::inherent_extrinsics(&factory_state);
	let inherents = client.runtime_api().inherent_extrinsics(&prior_block_id, inherents)
		.expect("Failed to create inherent extrinsics");

	let block = create_block::<RA, _, _, _, _>(&client, transfer, inherents);

	factory_state.set_block_no(factory_state.block_no() + RA::Number::one());

	info!(
		"Created block {} with hash {}. Transferring {} from {} to {}.",
		factory_state.block_no(),
		prior_block_hash,
		amount,
		from.0,
		to
	);

	Some(block)
}
