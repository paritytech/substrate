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

use std::time::{SystemTime, UNIX_EPOCH};

use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

use balances::Call as BalancesCall;
use keyring::sr25519::Keyring;
use keyring::sr25519::sr25519::Public;
use node_primitives::Hash;
use node_runtime::{Call, CheckedExtrinsic, UncheckedExtrinsic};
use primitives::sr25519;
use primitives::crypto::Pair;
use parity_codec::Encode;
use sr_primitives::generic::{Era, UncheckedMortalCompactExtrinsic};
use sr_primitives::traits::As;
use substrate_service::ServiceFactory;
use transaction_factory::RuntimeAdapter;
use crate::service;

pub struct RuntimeAdapterImpl;

impl RuntimeAdapter for RuntimeAdapterImpl {
	type AccountId = node_primitives::AccountId;
	type BlockNumber = node_primitives::BlockNumber;

	type Extrinsic = UncheckedMortalCompactExtrinsic<
		indices::address::Address<Public, u32>,
		u64,
		node_runtime::Call,
		sr_primitives::AnySignature
	>;

	type Balance = node_primitives::Balance;
	type Moment = node_primitives::Timestamp;
	type Hash = node_primitives::Hash;
	type BlockId = node_primitives::BlockId;
	type Index = node_primitives::Index;
	type Phase = sr_primitives::generic::Phase;
	type Secret = sr25519::Pair;
	type Header = node_primitives::Header;

	fn transfer_extrinsic(
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: Self::Balance,
		index: Self::Index,
		phase: Self::Phase,
		prior_block_hash: &Self::Hash,
	) -> Self::Extrinsic {
		sign::<service::Factory>(CheckedExtrinsic {
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

	fn timestamp_inherent(
		ts: Self::Moment,
		key: Self::Secret,
		phase: Self::Phase,
		prior_block_hash: &Self::Hash,
	) -> Self::Extrinsic {
		let cex = CheckedExtrinsic {
			signed: None,
			function: Call::Timestamp(timestamp::Call::set(ts)),
		};
		let timestamp = sign::<service::Factory>(cex, &key, &prior_block_hash, phase.as_());
		timestamp
	}

	fn minimum_balance() -> Self::Balance {
		// TODO get correct amount via api
		1337
	}

	fn minimum_period() -> Self::Moment {
		// TODO get minimum_period via api: <timestamp::Module<T>>::minimum_period()
		99
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

	fn extract_timestamp(_block_hash: Self::Hash) -> Self::Moment {
		// TODO get correct timestamp from inherent
		let now = SystemTime::now();
		now.duration_since(UNIX_EPOCH)
			.expect("Time went backwards").as_secs()
	}

	fn extract_index(_account_id: Self::AccountId, _block_hash: Self::Hash) -> Self::Index {
		// TODO get correct index for account via api
		0.as_()
	}

	fn extract_phase(_block_hash: Self::Hash) -> Self::Phase {
		// TODO get correct phase via api
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
fn sign<F: ServiceFactory>(
	xt: CheckedExtrinsic,
	key: &sr25519::Pair,
	prior_block_hash: &Hash,
	phase: u64,
) -> UncheckedExtrinsic {
	match xt.signed {
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
	}
}

