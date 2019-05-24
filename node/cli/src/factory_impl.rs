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

//! Implementation of the transaction factory trait, which enables
//! using the cli to manufacture transactions and distribute them
//! to accounts.

use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

use balances::Call as BalancesCall;
use parity_codec::Decode;
use keyring::sr25519::Keyring;
use node_primitives::Hash;
use node_runtime::{Call, CheckedExtrinsic, UncheckedExtrinsic};
use primitives::sr25519;
use primitives::crypto::Pair;
use parity_codec::Encode;
use sr_primitives::generic::Era;
use sr_primitives::traits::{As, Block as BlockT, Header as HeaderT};
use substrate_service::ServiceFactory;
use transaction_factory::{RuntimeAdapter, FactoryState};
use crate::service;
use inherents::InherentData;
use timestamp;
use finality_tracker;

pub struct RuntimeAdapterImpl;

// TODO get via api: <timestamp::Module<T>>::minimum_period(). See #2587.
const MINIMUM_PERIOD: u64 = 99;

impl RuntimeAdapter for RuntimeAdapterImpl {
	type AccountId = node_primitives::AccountId;
	type Balance = node_primitives::Balance;
	type Index = node_primitives::Index;
	type Phase = sr_primitives::generic::Phase;
	type Secret = sr25519::Pair;
	type Block = node_primitives::Block;

	fn transfer_extrinsic(
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: Self::Balance,
		index: Self::Index,
		phase: Self::Phase,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic {
		sign::<service::Factory, Self>(CheckedExtrinsic {
			signed: Some((sender.clone(), index)),
			function: Call::Balances(
				BalancesCall::transfer(
					indices::address::Address::Id(
						destination.clone().into()
					),
					amount.into()
				)
			)
		}, key, &prior_block_hash, phase.as_())
	}

	fn inherent_extrinsics(
		curr: &FactoryState
	) -> InherentData {
		let no = <<Self::Block as BlockT>::Header as HeaderT>::Number::sa(curr.block_no);
		let timestamp = no * MINIMUM_PERIOD;

		let mut inherent = InherentData::new();
		inherent.put_data(timestamp::INHERENT_IDENTIFIER, &timestamp)
			.expect("timestamp put data");
		inherent.put_data(finality_tracker::INHERENT_IDENTIFIER, &no)
			.expect("finality put data");
		inherent
	}

	fn minimum_balance() -> Self::Balance {
		// TODO get correct amount via api. See #2587.
		1337
	}

	fn master_account_id() -> Self::AccountId {
		Keyring::Alice.pair().public()
	}

	fn master_account_secret() -> Self::Secret {
		Keyring::Alice.pair()
	}

	/// Generates a random `AccountId` from `seed`.
	fn gen_random_account_id(seed: u64) -> Self::AccountId {
		let pair: sr25519::Pair = sr25519::Pair::from_seed(gen_seed_bytes(seed));
		pair.public().into()
	}

	/// Generates a random `Secret` from `seed`.
	fn gen_random_account_secret(seed: u64) -> Self::Secret {
		let pair: sr25519::Pair = sr25519::Pair::from_seed(gen_seed_bytes(seed));
		pair
	}

	fn extract_index(
		_account_id: Self::AccountId,
		_block_hash: <Self::Block as BlockT>::Hash,
	) -> Self::Index {
		// TODO get correct index for account via api. See #2587.
		0.as_()
	}

	fn extract_phase(_block_hash: <Self::Block as BlockT>::Hash) -> Self::Phase {
		// TODO get correct phase via api. See #2587.
		0.as_()
	}
}

fn gen_seed_bytes(seed: u64) -> [u8; 32] {
	let mut rng: StdRng = SeedableRng::seed_from_u64(seed);

	let mut seed_bytes = [0u8; 32];
	for i in 0..32 {
		seed_bytes[i] = rng.gen::<u8>();
	}
	seed_bytes
}

/// Creates an `UncheckedExtrinsic` containing the appropriate signature for
/// a `CheckedExtrinsics`.
fn sign<F: ServiceFactory, RA: RuntimeAdapter>(
	xt: CheckedExtrinsic,
	key: &sr25519::Pair,
	prior_block_hash: &Hash,
	phase: u64,
) -> <RA::Block as BlockT>::Extrinsic {
	let s = match xt.signed {
		Some((signed, index)) => {
			let era = Era::mortal(256, phase);
			let payload = (index.into(), xt.function, era, prior_block_hash);
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
	};

	let e = Encode::encode(&s);
	Decode::decode(&mut &e[..]).expect("Failed to decode signed unchecked extrinsic")
}
