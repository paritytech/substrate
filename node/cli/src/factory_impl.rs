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

use codec::{Encode, Decode};
use keyring::sr25519::Keyring;
use node_runtime::{Call, CheckedExtrinsic, UncheckedExtrinsic, SignedExtra, BalancesCall, ExistentialDeposit};
use primitives::{sr25519, crypto::Pair};
use sr_primitives::{generic::Era, traits::{Block as BlockT, Header as HeaderT, SignedExtension}};
use transaction_factory::RuntimeAdapter;
use transaction_factory::modes::Mode;
use inherents::InherentData;
use timestamp;
use finality_tracker;

// TODO get via api: <T as timestamp::Trait>::MinimumPeriod::get(). See #2587.
const MINIMUM_PERIOD: u64 = 99;

pub struct FactoryState<N> {
	block_no: N,

	mode: Mode,
	start_number: u32,
	rounds: u32,
	round: u32,
	block_in_round: u32,
	num: u32,
}

type Number = <<node_primitives::Block as BlockT>::Header as HeaderT>::Number;

impl<Number> FactoryState<Number> {
	fn build_extra(index: node_primitives::Index, phase: u64) -> node_runtime::SignedExtra {
		(
			system::CheckVersion::new(),
			system::CheckGenesis::new(),
			system::CheckEra::from(Era::mortal(256, phase)),
			system::CheckNonce::from(index),
			system::CheckWeight::new(),
			balances::TakeFees::from(0)
		)
	}
}

impl RuntimeAdapter for FactoryState<Number> {
	type AccountId = node_primitives::AccountId;
	type Balance = node_primitives::Balance;
	type Block = node_primitives::Block;
	type Phase = sr_primitives::generic::Phase;
	type Secret = sr25519::Pair;
	type Index = node_primitives::Index;

	type Number = Number;

	fn new(
		mode: Mode,
		num: u64,
		rounds: u64,
	) -> FactoryState<Self::Number> {
		FactoryState {
			mode,
			num: num as u32,
			round: 0,
			rounds: rounds as u32,
			block_in_round: 0,
			block_no: 0,
			start_number: 0,
		}
	}

	fn block_no(&self) -> Self::Number {
		self.block_no
	}

	fn block_in_round(&self) -> Self::Number {
		self.block_in_round
	}

	fn rounds(&self) -> Self::Number {
		self.rounds
	}

	fn num(&self) -> Self::Number {
		self.num
	}

	fn round(&self) -> Self::Number {
		self.round
	}

	fn start_number(&self) -> Self::Number {
		self.start_number
	}

	fn mode(&self) -> &Mode {
		&self.mode
	}

	fn set_block_no(&mut self, val: Self::Number) {
		self.block_no = val;
	}

	fn set_block_in_round(&mut self, val: Self::Number) {
		self.block_in_round = val;
	}

	fn set_round(&mut self, val: Self::Number) {
		self.round = val;
	}

	fn transfer_extrinsic(
		&self,
		sender: &Self::AccountId,
		key: &Self::Secret,
		destination: &Self::AccountId,
		amount: &Self::Balance,
		version: u32,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic {
		let index = self.extract_index(&sender, prior_block_hash);
		let phase = self.extract_phase(*prior_block_hash);
		sign::<Self>(CheckedExtrinsic {
			signed: Some((sender.clone(), Self::build_extra(index, phase))),
			function: Call::Balances(
				BalancesCall::transfer(
					indices::address::Address::Id(destination.clone().into()),
					(*amount).into()
				)
			)
		}, key, (version, genesis_hash.clone(), prior_block_hash.clone(), (), (), ()))
	}

	fn inherent_extrinsics(&self) -> InherentData {
		let timestamp = self.block_no as u64 * MINIMUM_PERIOD;

		let mut inherent = InherentData::new();
		inherent.put_data(timestamp::INHERENT_IDENTIFIER, &timestamp)
			.expect("Failed putting timestamp inherent");
		inherent.put_data(finality_tracker::INHERENT_IDENTIFIER, &self.block_no)
			.expect("Failed putting finalized number inherent");
		inherent
	}

	fn minimum_balance() -> Self::Balance {
		// TODO get correct amount via api. See #2587.
		ExistentialDeposit::get()
	}

	fn master_account_id() -> Self::AccountId {
		Keyring::Alice.pair().public()
	}

	fn master_account_secret() -> Self::Secret {
		Keyring::Alice.pair()
	}

	/// Generates a random `AccountId` from `seed`.
	fn gen_random_account_id(seed: &Self::Number) -> Self::AccountId {
		let pair: sr25519::Pair = sr25519::Pair::from_seed(&gen_seed_bytes(*seed));
		pair.public().into()
	}

	/// Generates a random `Secret` from `seed`.
	fn gen_random_account_secret(seed: &Self::Number) -> Self::Secret {
		let pair: sr25519::Pair = sr25519::Pair::from_seed(&gen_seed_bytes(*seed));
		pair
	}

	fn extract_index(
		&self,
		_account_id: &Self::AccountId,
		_block_hash: &<Self::Block as BlockT>::Hash,
	) -> Self::Index {
		// TODO get correct index for account via api. See #2587.
		// This currently prevents the factory from being used
		// without a preceding purge of the database.
		if self.mode == Mode::MasterToN || self.mode == Mode::MasterTo1 {
			self.block_no() as Self::Index
		} else {
			match self.round() {
				0 =>
					// if round is 0 all transactions will be done with master as a sender
					self.block_no() as Self::Index,
				_ =>
					// if round is e.g. 1 every sender account will be new and not yet have
					// any transactions done
					0
			}
		}
	}

	fn extract_phase(
		&self,
		_block_hash: <Self::Block as BlockT>::Hash
	) -> Self::Phase {
		// TODO get correct phase via api. See #2587.
		// This currently prevents the factory from being used
		// without a preceding purge of the database.
		self.block_no() as Self::Phase
	}
}

fn gen_seed_bytes(seed: u32) -> [u8; 32] {
	let mut rng: StdRng = SeedableRng::seed_from_u64(seed as u64);

	let mut seed_bytes = [0u8; 32];
	for i in 0..32 {
		seed_bytes[i] = rng.gen::<u8>();
	}
	seed_bytes
}

/// Creates an `UncheckedExtrinsic` containing the appropriate signature for
/// a `CheckedExtrinsics`.
fn sign<RA: RuntimeAdapter>(
	xt: CheckedExtrinsic,
	key: &sr25519::Pair,
	additional_signed: <SignedExtra as SignedExtension>::AdditionalSigned,
) -> <RA::Block as BlockT>::Extrinsic {
	let s = match xt.signed {
		Some((signed, extra)) => {
			let payload = (xt.function, extra.clone(), additional_signed);
			let signature = payload.using_encoded(|b| {
				if b.len() > 256 {
					key.sign(&sr_io::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((indices::address::Address::Id(signed), signature, extra)),
				function: payload.0,
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
