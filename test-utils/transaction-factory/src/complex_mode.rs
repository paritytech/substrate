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
use sr_primitives::traits::{As, Block as BlockT, ProvideRuntimeApi};
use substrate_service::{FactoryBlock, FullClient, ServiceFactory, ComponentClient, FullComponents};

use crate::{FactoryState, RuntimeAdapter, create_block};

pub fn next<F, RA>(
	curr: &mut FactoryState,
	client: &Arc<ComponentClient<FullComponents<F>>>,
	prior_block_hash: <RA::Block as BlockT>::Hash,
	last_ts: RA::Moment,
) -> Option<(RA::Moment, <F as ServiceFactory>::Block)>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,

	RA: RuntimeAdapter,
{
	if !(curr.block_no < curr.num * curr.rounds && curr.round < curr.rounds) {
		return None;
	}

	info!(
		"Round {}: Creating {} transactions in total, {} per round. {} rounds in total.",
		curr.round + 1,
		curr.num * curr.rounds,
		curr.num,
		curr.rounds,
	);

	let from = from::<RA>(curr);

	let seed = curr.start_number + curr.block_no;
	let to = RA::gen_random_account_id(seed);

	let amount = match curr.round {
		0 => RA::minimum_balance().as_() * curr.rounds,
		_ => {
			let rounds_left = curr.rounds - curr.round;
			RA::minimum_balance().as_() * rounds_left
		}
	};

	let transfer = RA::transfer_extrinsic(
		&from.0,
		&from.1,
		&to,
		RA::Balance::sa(amount),
		RA::Index::sa(curr.index),
		RA::Phase::sa(curr.phase),
		&prior_block_hash,
	);

	let new_ts = last_ts + RA::minimum_period();
	let timestamp = RA::timestamp_inherent(
		new_ts.clone(),
		RA::master_account_secret(),
		RA::Phase::sa(curr.phase),
		&prior_block_hash
	);

	let block = create_block::<F, RA>(&client, transfer, timestamp);
	info!(
		"Created block {} with hash {}. Transferring {} from {} to {}.",
		curr.block_no + 1,
		prior_block_hash,
		amount,
		from.0,
		to
	);

	curr.block_no += 1;

	let new_round = curr.block_no > 0 && curr.block_no % curr.num == 0;
	if new_round {
		curr.round += 1;
		curr.block_in_round = 0;
	} else {
		curr.block_in_round += 1;
	}

	curr.phase += 1;

	curr.index = match curr.round {
		// if round is 0 all transactions will be done with master as a sender
		0 => curr.index + 1,

		// if round is 1 every sender account will be new and not yet have any
		// transactions done
		_ => 0,
	};

	Some((new_ts, block))
}

/// Return the account which received tokens at this point in the previous round.
fn from<RA>(
	curr: &mut FactoryState
) -> (<RA as RuntimeAdapter>::AccountId, <RA as RuntimeAdapter>::Secret)
where RA: RuntimeAdapter
{
	match curr.round {
		0 => {
			// first round always uses master account
			(RA::master_account_id(), RA::master_account_secret())
		},
		_ => {
			// the account to which was sent in the last round
			let seed = match curr.round {
				1 => curr.start_number + curr.block_in_round,
				_ => {
					let block_no_in_prior_round = curr.num * (curr.round - 1) + curr.block_in_round;
					curr.start_number + block_no_in_prior_round
				}
			};
			(RA::gen_random_account_id(seed), RA::gen_random_account_secret(seed))
		},
	}
}
