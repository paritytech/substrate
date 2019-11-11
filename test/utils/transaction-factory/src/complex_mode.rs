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

/// This module implements the `MasterToNToM` mode:
///
/// Manufacture `num` transactions from the master account to `num`
/// randomly created accounts. From each of these randomly created
/// accounts manufacture a transaction to another randomly created
/// account.
/// Repeat this round `rounds` times. If `rounds` = 1 the behavior
/// is the same as `MasterToN`.
///
///   A -> B
///   A -> C
///   A -> D
///   ... x `num`
///
///   B -> E
///   C -> F
///   D -> G
///   ...
///   E -> H
///   F -> I
///   G -> J
///   ...
///   ... x `rounds`

use std::sync::Arc;

use log::info;
use client::Client;
use block_builder_api::BlockBuilder;
use sr_api::ConstructRuntimeApi;
use primitives::{Blake2Hasher, Hasher};
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{Block as BlockT, ProvideRuntimeApi, One, Zero};

use crate::{RuntimeAdapter, create_block};

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
	Backend: client::backend::Backend<Block, Blake2Hasher> + Send,
	Client<Backend, Exec, Block, RtApi>: ProvideRuntimeApi,
	<Client<Backend, Exec, Block, RtApi> as ProvideRuntimeApi>::Api:
		BlockBuilder<Block, Error = client::error::Error>,
	RtApi: ConstructRuntimeApi<Block, Client<Backend, Exec, Block, RtApi>> + Send + Sync,
	RA: RuntimeAdapter,
{
	let total = factory_state.start_number() + factory_state.num() * factory_state.rounds();

	if factory_state.block_no() >= total || factory_state.round() >= factory_state.rounds() {
		return None;
	}

	info!(
		"Round {}: Creating {} transactions in total, {} per round. {} rounds in total.",
		factory_state.round() + RA::Number::one(),
		factory_state.num() * factory_state.rounds(),
		factory_state.num(),
		factory_state.rounds(),
	);

	let from = from::<RA>(factory_state);

	let seed = factory_state.start_number() + factory_state.block_no();
	let to = RA::gen_random_account_id(&seed);

	let rounds_left = factory_state.rounds() - factory_state.round();
	let amount = RA::minimum_balance() * rounds_left.into();

	let transfer = factory_state.transfer_extrinsic(
		&from.0,
		&from.1,
		&to,
		&amount,
		version,
		&genesis_hash,
		&prior_block_hash,
	);

	let inherents = factory_state.inherent_extrinsics();
	let inherents = client.runtime_api().inherent_extrinsics(&prior_block_id, inherents)
		.expect("Failed to create inherent extrinsics");

	let block = create_block::<RA, _, _, _, _>(&client, transfer, inherents);
	info!(
		"Created block {} with hash {}. Transferring {} from {} to {}.",
		factory_state.block_no() + RA::Number::one(),
		prior_block_hash,
		amount,
		from.0,
		to
	);

	factory_state.set_block_no(factory_state.block_no() + RA::Number::one());

	let new_round = factory_state.block_no() > RA::Number::zero()
		&& factory_state.block_no() % factory_state.num() == RA::Number::zero();
	if new_round {
		factory_state.set_round(factory_state.round() + RA::Number::one());
		factory_state.set_block_in_round(RA::Number::zero());
	} else {
		factory_state.set_block_in_round(factory_state.block_in_round() + RA::Number::one());
	}

	Some(block)
}

/// Return the account which received tokens at this point in the previous round.
fn from<RA>(
	factory_state: &mut RA
) -> (<RA as RuntimeAdapter>::AccountId, <RA as RuntimeAdapter>::Secret)
where RA: RuntimeAdapter
{
	let is_first_round = factory_state.round() == RA::Number::zero();
	match is_first_round {
		true => {
			// first round always uses master account
			(RA::master_account_id(), RA::master_account_secret())
		},
		_ => {
			// the account to which was sent in the last round
			let is_round_one = factory_state.round() == RA::Number::one();
			let seed = match is_round_one {
				true => factory_state.start_number() + factory_state.block_in_round(),
				_ => {
					let block_no_in_prior_round =
						factory_state.num() * (factory_state.round() - RA::Number::one()) + factory_state.block_in_round();
					factory_state.start_number() + block_no_in_prior_round
				}
			};
			(RA::gen_random_account_id(&seed), RA::gen_random_account_secret(&seed))
		},
	}
}
