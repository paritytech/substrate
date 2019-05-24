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
use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use sr_primitives::traits::{As, Block as BlockT, ProvideRuntimeApi};
use sr_primitives::generic::BlockId;
use substrate_service::{FactoryBlock, FullClient, ServiceFactory, ComponentClient, FullComponents};

use crate::{FactoryState, Mode, RuntimeAdapter, create_block};

pub fn next<F, RA>(
	curr: &mut FactoryState,
	client: &Arc<ComponentClient<FullComponents<F>>>,
	prior_block_hash: <RA::Block as BlockT>::Hash,
	prior_block_id: BlockId<F::Block>,
) -> Option<<F as ServiceFactory>::Block>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,
	RA: RuntimeAdapter,
{
	if curr.block_no >= curr.num {
		return None;
	}

	let from = (RA::master_account_id(), RA::master_account_secret());

	let seed = match curr.mode {
		// choose the same receiver for all transactions
		Mode::MasterTo1 => curr.start_number,

		// different receiver for each transaction
		Mode::MasterToN => curr.start_number + curr.block_no,
		_ => unreachable!("Mode not covered!"),
	};
	let to = RA::gen_random_account_id(seed);

	let amount = RA::minimum_balance().as_();

	let transfer = RA::transfer_extrinsic(
		&from.0,
		&from.1,
		&to,
		RA::Balance::sa(amount),
		RA::Index::sa(curr.index),
		RA::Phase::sa(curr.phase),
		&prior_block_hash,
	);

	let inherents = RA::inherent_extrinsics(&curr);
	let inherents = client.runtime_api().inherent_extrinsics(&prior_block_id, inherents)
		.expect("Failed to create inherent extrinsics");

	let block = create_block::<F, RA>(&client, transfer, inherents);
	info!(
		"Created block {} with hash {}. Transferring {} from {} to {}.",
		curr.block_no + 1,
		prior_block_hash,
		amount,
		from.0,
		to
	);

	curr.block_no += 1;
	curr.phase += 1;
	curr.index += 1;

	Some(block)
}
