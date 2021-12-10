// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! A set of benchmarks which can establish a global baseline for all other
//! benchmarking.

#![cfg(feature = "runtime-benchmarks")]

use crate::benchmarks;
use codec::Encode;
use frame_system::Pallet as System;
use sp_application_crypto::KeyTypeId;
use sp_runtime::{
	traits::{AppVerify, Hash},
	RuntimeAppPublic,
};
use sp_std::prelude::*;

pub const TEST_KEY_TYPE_ID: KeyTypeId = KeyTypeId(*b"test");

mod app_sr25519 {
	use super::TEST_KEY_TYPE_ID;
	use sp_application_crypto::{app_crypto, sr25519};
	app_crypto!(sr25519, TEST_KEY_TYPE_ID);
}

type SignerId = app_sr25519::Public;

pub struct Pallet<T: Config>(System<T>);
pub trait Config: frame_system::Config {}

benchmarks! {
	addition {
		let i in 0 .. 1_000_000;
		let mut start = 0;
	}: {
		(0..i).for_each(|_| start += 1);
	} verify {
		assert_eq!(start, i);
	}

	subtraction {
		let i in 0 .. 1_000_000;
		let mut start = u32::MAX;
	}: {
		(0..i).for_each(|_| start -= 1);
	} verify {
		assert_eq!(start, u32::MAX - i);
	}

	multiplication {
		let i in 0 .. 1_000_000;
		let mut out = 0;
	}:  {
		(1..=i).for_each(|j| out = 2 * j);
	} verify {
		assert_eq!(out, 2 * i);
	}

	division {
		let i in 0 .. 1_000_000;
		let mut out = 0;
	}: {
		(0..=i).for_each(|j| out = j / 2);
	} verify {
		assert_eq!(out, i / 2);
	}

	hashing {
		let i in 0 .. 100;
		let mut hash = T::Hash::default();
	}: {
		(0..=100_000u32).for_each(|j| hash = T::Hashing::hash(&j.to_be_bytes()));
	} verify {
		assert!(hash != T::Hash::default());
	}

	sr25519_verification {
		let i in 1 .. 100;

		let public = SignerId::generate_pair(None);

		let sigs_count: u8 = i.try_into().unwrap();
		let msg_and_sigs: Vec<_> = (0..sigs_count).map(|j| {
			let msg = vec![j, j];
			(msg.clone(), public.sign(&msg).unwrap())
		})
		.collect();
	}: {
		msg_and_sigs.iter().for_each(|(msg, sig)| {
			assert!(sig.verify(&msg[..], &public));
		});
	}

	#[skip_meta]
	storage_read {
		let i in 0 .. 1_000;
		let mut people = Vec::new();
		(0..i).for_each(|j| {
			let hash = T::Hashing::hash(&j.to_be_bytes()).encode();
			frame_support::storage::unhashed::put(&hash, &hash);
			people.push(hash);
		});
	}: {
		people.iter().for_each(|hash| {
			// This does a storage read
			let value = frame_support::storage::unhashed::get(hash);
			assert_eq!(value, Some(hash.to_vec()));
		});
	}

	#[skip_meta]
	storage_write {
		let i in 0 .. 1_000;
		let mut hashes = Vec::new();
		(0..i).for_each(|j| {
			let hash = T::Hashing::hash(&j.to_be_bytes());
			hashes.push(hash.encode());
		});
	}: {
		hashes.iter().for_each(|hash| {
			// This does a storage write
			frame_support::storage::unhashed::put(hash, hash);
		});
	} verify {
		hashes.iter().for_each(|hash| {
			let value = frame_support::storage::unhashed::get(hash);
			assert_eq!(value, Some(hash.to_vec()));
		});
	}

	impl_benchmark_test_suite!(
		Pallet,
		crate::baseline::mock::new_test_ext(),
		crate::baseline::mock::Test,
	);
}

#[cfg(test)]
pub mod mock {
	use sp_runtime::{testing::H256, traits::IdentityLookup};

	type AccountId = u64;
	type AccountIndex = u32;
	type BlockNumber = u64;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		}
	);

	impl frame_system::Config for Test {
		type BaseCallFilter = frame_support::traits::Everything;
		type BlockWeights = ();
		type BlockLength = ();
		type DbWeight = ();
		type Origin = Origin;
		type Index = AccountIndex;
		type BlockNumber = BlockNumber;
		type Call = Call;
		type Hash = H256;
		type Hashing = ::sp_runtime::traits::BlakeTwo256;
		type AccountId = AccountId;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = sp_runtime::testing::Header;
		type Event = Event;
		type BlockHashCount = ();
		type Version = ();
		type PalletInfo = PalletInfo;
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
		type SystemWeightInfo = ();
		type SS58Prefix = ();
		type OnSetCode = ();
		type MaxConsumers = frame_support::traits::ConstU32<16>;
	}

	impl super::Config for Test {}

	pub fn new_test_ext() -> sp_io::TestExternalities {
		use sp_keystore::{testing::KeyStore, KeystoreExt, SyncCryptoStorePtr};
		use sp_std::sync::Arc;

		let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		let mut ext = sp_io::TestExternalities::new(t);
		ext.register_extension(KeystoreExt(Arc::new(KeyStore::new()) as SyncCryptoStorePtr));

		ext
	}
}
