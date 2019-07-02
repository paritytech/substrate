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
use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{Block as BlockT, ProvideRuntimeApi, One, Zero};
use substrate_service::{
	FactoryBlock, FullClient, ServiceFactory, ComponentClient, FullComponents
};

use crate::{RuntimeAdapter, create_block};

pub fn next<F, RA>(
	factory_state: &mut RA,
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

	let amount;
	if factory_state.round() == RA::Number::zero() {
		amount = RA::minimum_balance() * factory_state.rounds();
	} else {
		let rounds_left = factory_state.rounds() - factory_state.round();
		amount = RA::minimum_balance() * rounds_left;
	};

	let transfer = factory_state.transfer_extrinsic(
		&from.0,
		&from.1,
		&to,
		&amount,
		&prior_block_hash,
	);

	let inherents = factory_state.inherent_extrinsics();
	let inherents = client.runtime_api().inherent_extrinsics(&prior_block_id, inherents)
		.expect("Failed to create inherent extrinsics");

	let block = create_block::<F, RA>(&client, transfer, inherents);
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
