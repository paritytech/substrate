// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate as example_offchain_worker;
use crate::*;
use pallet::config_preludes::*;
use codec::Decode;
use frame_support::{
	assert_ok, derive_impl,
	traits::{ConstU32, ConstU64},
};
use sp_core::{
	offchain::{testing, OffchainWorkerExt, TransactionPoolExt},
	sr25519::Signature,
	H256,
};

use sp_api_hidden_includes_construct_runtime::hidden_include::traits::Hooks;
use sp_keystore::{testing::MemoryKeystore, Keystore, KeystoreExt};
use sp_runtime::{
	testing::TestXt,
	traits::{BlakeTwo256, Extrinsic as ExtrinsicT, IdentifyAccount, IdentityLookup, Verify},
	RuntimeAppPublic,
};
use frame_system::pallet_prelude::BlockNumberFor;

type Block = frame_system::mocking::MockBlock<Test>;

// For testing the module, we construct a mock runtime.
frame_support::construct_runtime!(
	pub enum Test
	{
		System: frame_system::{Pallet, Call, Config<T>, Storage, Event<T>},
		PingPongOcwExample: example_offchain_worker::{Pallet, Call, Storage, Event<T>, ValidateUnsigned},
	}
);

impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type RuntimeOrigin = RuntimeOrigin;
	type RuntimeCall = RuntimeCall;
	type Nonce = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Block = Block;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = ConstU32<16>;
}

type Extrinsic = TestXt<RuntimeCall, ()>;
type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

impl frame_system::offchain::SigningTypes for Test {
	type Public = <Signature as Verify>::Signer;
	type Signature = Signature;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test
where
	RuntimeCall: From<LocalCall>,
{
	type OverarchingCall = RuntimeCall;
	type Extrinsic = Extrinsic;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Test
where
	RuntimeCall: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: RuntimeCall,
		_public: <Signature as Verify>::Signer,
		_account: AccountId,
		nonce: u64,
	) -> Option<(RuntimeCall, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
		Some((call, (nonce, ())))
	}
}


#[derive_impl(TestDefaultConfig as pallet::DefaultConfig)]
impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type AuthorityId = crypto::TestAuthId;
	type UnsignedInterval = ConstU64<16>;
}

fn user_pub() -> sp_core::sr25519::Public {
	sp_core::sr25519::Public::from_raw([1u8; 32])
}

pub fn run_to_block(n: u64) {
	while System::block_number() < n {
		if System::block_number() > 1 {
			PingPongOcwExample::on_finalize(System::block_number());
			System::on_finalize(System::block_number());
		}
		System::set_block_number(System::block_number() + 1);
		System::on_initialize(System::block_number());
		PingPongOcwExample::on_initialize(System::block_number());
	}
}

#[test]
fn it_aggregates_pings() {
	sp_io::TestExternalities::default().execute_with(|| {
		System::set_block_number(1);

		assert_eq!(PingPongOcwExample::pings().len(), 0);

		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), 69));
		assert_eq!(PingPongOcwExample::pings().len(), 1);

		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), 42));
		assert_eq!(PingPongOcwExample::pings().len(), 2);

		// advance the block number so that the ping is no longer valid
		run_to_block(System::block_number() + 1);

		assert_eq!(PingPongOcwExample::pings().len(), 0);
	});
}

#[test]
fn should_submit_signed_transaction_on_chain() {
	const NONCE: u32 = 69;
	const PHRASE: &str =
		"news slush supreme milk chapter athlete soap sausage put clutch what kitten";

	let (offchain, _offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = MemoryKeystore::new();
	keystore
		.sr25519_generate_new(crate::crypto::Public::ID, Some(&format!("{}/hunter1", PHRASE)))
		.unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainWorkerExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt::new(keystore));

	t.execute_with(|| {
		// user sends ping
		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), NONCE));
		// when
		PingPongOcwExample::ocw_pong_signed().unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature.unwrap().0, 0);
		assert_eq!(
			tx.call,
			RuntimeCall::PingPongOcwExample(crate::Call::pong_signed { nonce: NONCE })
		);
	});
}

#[test]
fn should_submit_unsigned_transaction_on_chain_for_any_account() {
	const NONCE: u32 = 69;
	const PHRASE: &str =
		"news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, _offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = MemoryKeystore::new();

	keystore
		.sr25519_generate_new(crate::crypto::Public::ID, Some(&format!("{}/hunter1", PHRASE)))
		.unwrap();

	let public_key = *keystore.sr25519_public_keys(crate::crypto::Public::ID).get(0).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainWorkerExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt::new(keystore));

	let pong_payload = PongPayload {
		block_number: 1,
		nonce: NONCE,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	t.execute_with(|| {
		// user sends ping
		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), NONCE));
		// when
		PingPongOcwExample::ocw_pong_unsigned_for_any_account(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let RuntimeCall::PingPongOcwExample(crate::Call::pong_unsigned_with_signed_payload {
			pong_payload: body,
			signature,
		}) = tx.call
		{
			assert_eq!(body, pong_payload);

			let signature_valid =
				<PongPayload<
					<Test as SigningTypes>::Public,
					BlockNumberFor<Test>,
				> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&pong_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_unsigned_transaction_on_chain_for_all_accounts() {
	const NONCE: u32 = 69;
	const PHRASE: &str =
		"news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, _offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = MemoryKeystore::new();

	keystore
		.sr25519_generate_new(crate::crypto::Public::ID, Some(&format!("{}/hunter1", PHRASE)))
		.unwrap();

	let public_key = *keystore.sr25519_public_keys(crate::crypto::Public::ID).get(0).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainWorkerExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt::new(keystore));

	let pong_payload = PongPayload {
		block_number: 1,
		nonce: NONCE,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	t.execute_with(|| {
		// user sends ping
		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), NONCE));
		// when
		PingPongOcwExample::ocw_pong_unsigned_for_all_accounts(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let RuntimeCall::PingPongOcwExample(crate::Call::pong_unsigned_with_signed_payload {
			pong_payload: body,
			signature,
		}) = tx.call
		{
			assert_eq!(body, pong_payload);

			let signature_valid =
				<PongPayload<
					<Test as SigningTypes>::Public,
					BlockNumberFor<Test>,
				> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&pong_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_raw_unsigned_transaction_on_chain() {
	const NONCE: u32 = 69;

	let (offchain, _offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = MemoryKeystore::new();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainWorkerExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt::new(keystore));

	t.execute_with(|| {
		// user sends ping
		assert_ok!(PingPongOcwExample::ping(RuntimeOrigin::signed(user_pub()), NONCE));
		// when
		PingPongOcwExample::ocw_pong_raw_unsigned(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		assert_eq!(
			tx.call,
			RuntimeCall::PingPongOcwExample(crate::Call::pong_unsigned {
				block_number: 1,
				nonce: NONCE
			})
		);
	});
}
