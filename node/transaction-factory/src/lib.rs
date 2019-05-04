// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Simple transaction factory which distributes tokens from Alice
//! to a specified number of newly created accounts.

#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(not(feature = "std"), feature(alloc))]

use std::collections::HashMap;
use std::time::{SystemTime, UNIX_EPOCH};

use log::info;
use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

use balances;
use balances::Call as BalancesCall;
use client::block_builder::api::BlockBuilder;
use client::runtime_api::ConstructRuntimeApi;
use consensus_common::{BlockOrigin, ImportBlock, ForkChoiceStrategy};
use consensus_common::block_import::BlockImport;
use indices;
use keyring::sr25519::Keyring;
use node_primitives::Hash;
use node_runtime::{Call, CheckedExtrinsic, UncheckedExtrinsic};
use parity_codec::{Decode, Encode};
use primitives::sr25519;
use primitives::crypto::Pair;
use sr_primitives::generic::Era;
use sr_primitives::traits::{As, Block, Header, ProvideRuntimeApi};
use substrate_service::{FactoryBlock, FactoryFullConfiguration, FullClient, new_client, ServiceFactory};

/// Generates a random `AccountId` from `seed`.
fn gen_random_account_id(seed: u64) -> node_primitives::AccountId {
	let mut rng: StdRng = SeedableRng::seed_from_u64(seed);

	let mut seed_bytes = [0u8; 32];
	for i in 0..32 {
		seed_bytes[i] = rng.gen::<u8>();
	}

	let pair: sr25519::Pair = sr25519::Pair::from_seed(seed_bytes);
	pair.public().into()
}

/// Creates an `UncheckedExtrinsic` containing the appropriate signature for
/// a `CheckedExtrinsics`.
fn sign<F: ServiceFactory>(xt: CheckedExtrinsic, prior_block_hash: Hash, block_no: u64) -> UncheckedExtrinsic {
	let mut phase = 0;
	if block_no > 0 {
		phase = block_no - 1;
	}

	match xt.signed {
		Some((signed, index)) => {
			let era = Era::mortal(256, phase);
			let payload = (index.into(), xt.function, era, prior_block_hash);
			let key = Keyring::from_public(&signed)
				.expect("Failed to create public key from signed");
			let signature = payload.using_encoded(|b| {
				if b.len() > 256 {
					key.sign(&sr_io::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((indices::address::Address::Id(signed), signature, payload.0, era)),
				function: payload.1,
			}
		}
		None => UncheckedExtrinsic {
			signature: None,
			function: xt.function,
		},
	}
}

/// Manufacture `num` transactions from Alice to `num` accounts.
pub fn factory<F>(
	config: FactoryFullConfiguration<F>,
	num: u64,
) -> cli::error::Result<()>
where
	F: ServiceFactory,
	F::RuntimeApi: ConstructRuntimeApi<FactoryBlock<F>, FullClient<F>>,
	FullClient<F>: ProvideRuntimeApi,
	<FullClient<F> as ProvideRuntimeApi>::Api: BlockBuilder<FactoryBlock<F>>,
{
	info!("Creating {} transactions...", num);

	let client = new_client::<F>(&config)?;

	let mut prior_block_hash = client.best_block_header()?.hash();

	// TODO extract timestamp from last block inherents via the api
	// 	let api = client.runtime_api(); ?
	// 	let block = client.block(&BlockId::Hash(prior_block_hash))?;
	let now = SystemTime::now();
	let mut last_ts: u64 = now.duration_since(UNIX_EPOCH)
		.expect("Time went backwards").as_secs();

	let start_number: u64 = client.info()?.chain.best_number.as_() + 1;
	let mut curr_block_no = start_number;
	while curr_block_no < start_number + num {
		info!("Creating block {}", curr_block_no);

		let mut block = client.new_block().expect("Failed to create new block");
		let alice: node_primitives::AccountId = Keyring::Alice.into();
		let to: node_primitives::AccountId = gen_random_account_id(curr_block_no);

		// index contains amount of prior transactions on this account
		// TODO fetch correct nonce via api
		let index = curr_block_no - 1;

		// TODO get amount via api from minimum balance
		let amount = 1337;

		let transfer = sign::<F>(CheckedExtrinsic {
			signed: Some((alice.into(), index)),
			function: Call::Balances(
				BalancesCall::transfer(
					indices::address::Address::Id(
						to.clone().into(),
					),
					amount
				)
			)
		}, prior_block_hash, curr_block_no);
		block.push(
			Decode::decode(&mut &transfer.encode()[..])
				.expect("Failed to decode transfer extrinsic")
		).unwrap();

		// TODO get minimum_period via api: <timestamp::Module<T>>::minimum_period()
		let minimum_period = 99;
		let new_ts = last_ts + minimum_period;
		last_ts = new_ts;
		let cex = CheckedExtrinsic {
			signed: None,
			function: Call::Timestamp(timestamp::Call::set(new_ts)),
		};
		let timestamp = sign::<F>(cex, prior_block_hash, curr_block_no);
		block.push(
			Decode::decode(&mut &timestamp.encode()[..])
				.expect("Failed to decode timestamp extrinsic")
		).expect("Failed to push timestamp inherent into block");

		let block = block.bake().expect("Failed to bake block");
		prior_block_hash = block.header().hash();

		info!(
			"Created block {} with hash {}. Transferring from Alice to {}.",
			curr_block_no,
			prior_block_hash,
			to
		);

		let import = ImportBlock {
			origin: BlockOrigin::File,
			header: block.header().clone(),
			post_digests: Vec::new(),
			body: Some(block.extrinsics().to_vec()),
			finalized: false,
			justification: None,
			auxiliary: Vec::new(),
			fork_choice: ForkChoiceStrategy::LongestChain,
		};
		client.import_block(import, HashMap::new()).expect("Failed to import block");

		info!("Imported block {}", curr_block_no);
		curr_block_no += 1;
	}

	info!("Finished importing {} blocks", curr_block_no-1);

	Ok(())
}
