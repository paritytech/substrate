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

//! Implementation of the transaction factory trait, which enables
//! using the cli to manufacture transactions and distribute them
//! to accounts.

use rand::{Rng, SeedableRng};
use rand::rngs::StdRng;

use codec::{Encode, Decode};
use sp_keyring::sr25519::Keyring;
use node_runtime::{
	Call, CheckedExtrinsic, UncheckedExtrinsic, SignedExtra,
	MinimumPeriod, ExistentialDeposit,
};
use node_primitives::Signature;
use sp_core::{sr25519, crypto::Pair};
use sp_runtime::{
	generic::Era,
	traits::{
		Block as BlockT, Header as HeaderT, SignedExtension, Verify, IdentifyAccount,
	}
};
use frame_support::benchmarking::GetModule;
use node_transaction_factory::RuntimeAdapter;
use node_transaction_factory::automata::Automaton;

use sp_inherents::InherentData;
use sp_timestamp;
use sp_finality_tracker;

type AccountPublic = <Signature as Verify>::Signer;
type Number = <<node_primitives::Block as BlockT>::Header as HeaderT>::Number;

pub struct RuntimeState {
	block_number: Number,
	start_number: u32,
	round: u32,
	block_in_round: u32,
	index: u32,
}

impl RuntimeState {
	fn build_extra(index: node_primitives::Index, phase: u64) -> node_runtime::SignedExtra {
		(
			frame_system::CheckVersion::new(),
			frame_system::CheckGenesis::new(),
			frame_system::CheckEra::from(Era::mortal(256, phase)),
			frame_system::CheckNonce::from(index),
			frame_system::CheckWeight::new(),
			pallet_transaction_payment::ChargeTransactionPayment::from(0),
			Default::default(),
		)
	}
}

impl RuntimeAdapter for RuntimeState {
	type AccountId = node_primitives::AccountId;
	type Balance = node_primitives::Balance;
	type Block = node_primitives::Block;
	type Phase = sp_runtime::generic::Phase;
	type Secret = sr25519::Pair;
	type Index = node_primitives::Index;
	type Number = Number;

	fn new() -> RuntimeState {
		RuntimeState {
			round: 0,
			block_in_round: 0,
			block_number: 0,
			start_number: 0,
			index: 0,
		}
	}

	fn index(&self) -> u32 {
		self.index
	}

	fn increase_index(&mut self) {
		self.index += 1;
	}

	fn block_number(&self) -> Self::Number {
		self.block_number
	}

	fn block_in_round(&self) -> Self::Number {
		self.block_in_round
	}

	fn round(&self) -> Self::Number {
		self.round
	}

	fn start_number(&self) -> Self::Number {
		self.start_number
	}

	fn set_block_number(&mut self, val: Self::Number) {
		self.block_number = val;
	}

	fn set_block_in_round(&mut self, val: Self::Number) {
		self.block_in_round = val;
	}

	fn set_round(&mut self, val: Self::Number) {
		self.round = val;
	}

	fn create_extrinsic(
		&mut self,
		sender: &Self::AccountId,
		module: String,
		extrinsic_name: String,
		key: &Self::Secret,
		runtime_version: u32,
		genesis_hash: &<Self::Block as BlockT>::Hash,
		prior_block_hash: &<Self::Block as BlockT>::Hash,
	) -> <Self::Block as BlockT>::Extrinsic {
		let phase = self.extract_phase(*prior_block_hash);
		let function = Call::get_module(&module, &extrinsic_name);
		let extrinsic = CheckedExtrinsic {
			signed: Some((sender.clone(), Self::build_extra(self.index, phase))),
			function,
		};
		let additional_signed = (
			runtime_version,
			genesis_hash.clone(),
			prior_block_hash.clone(),
			(), (), (), (),
		);
		sign::<Self>(extrinsic, key, additional_signed)
	}

	fn inherent_extrinsics(&self) -> InherentData {
		let timestamp = (self.block_number as u64 + 1) * MinimumPeriod::get();

		let mut inherent = InherentData::new();
		inherent.put_data(sp_timestamp::INHERENT_IDENTIFIER, &timestamp)
			.expect("Failed putting timestamp inherent");
		inherent.put_data(sp_finality_tracker::INHERENT_IDENTIFIER, &self.block_number)
			.expect("Failed putting finalized number inherent");
		inherent
	}

	fn minimum_balance() -> Self::Balance {
		ExistentialDeposit::get()
	}

	fn master_account_id() -> Self::AccountId {
		Keyring::Alice.to_account_id()
	}

	fn master_account_secret() -> Self::Secret {
		Keyring::Alice.pair()
	}

	/// Generates a random `AccountId` from `seed`.
	fn gen_random_account_id(seed: &Self::Number) -> Self::AccountId {
		let pair: sr25519::Pair = sr25519::Pair::from_seed(&gen_seed_bytes(*seed));
		AccountPublic::from(pair.public()).into_account()
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
		0
	}

	fn extract_phase(
		&self,
		_block_hash: <Self::Block as BlockT>::Hash
	) -> Self::Phase {
		// TODO get correct phase via api. See #2587.
		// This currently prevents the factory from being used
		// without a preceding purge of the database.
		self.block_number() as Self::Phase
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
					key.sign(&sp_io::hashing::blake2_256(b))
				} else {
					key.sign(b)
				}
			}).into();
			UncheckedExtrinsic {
				signature: Some((pallet_indices::address::Address::Id(signed), signature, extra)),
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
