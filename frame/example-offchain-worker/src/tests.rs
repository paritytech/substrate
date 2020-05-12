// Copyright 2020 Parity Technologies (UK) Ltd.
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

use crate::*;

use codec::{Encode, Decode};
use frame_support::{
	assert_ok, impl_outer_origin, parameter_types,
	weights::Weight,
};
use sp_core::{
	H256,
	offchain::{OffchainExt, TransactionPoolExt, testing},
	sr25519::Signature,
	testing::KeyStore,
	traits::KeystoreExt,
};
use sp_runtime::{
	Perbill, RuntimeAppPublic,
	testing::{Header, TestXt},
	traits::{
		BlakeTwo256, IdentityLookup, Extrinsic as ExtrinsicT,
		IdentifyAccount, Verify,
	},
};

impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system {}
}

// For testing the module, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of modules we want to use.
#[derive(Clone, Eq, PartialEq, Encode, Decode)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MaximumBlockWeight: Weight = 1024;
	pub const MaximumBlockLength: u32 = 2 * 1024;
	pub const AvailableBlockRatio: Perbill = Perbill::one();
}
impl frame_system::Trait for Test {
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = sp_core::sr25519::Public;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type DbWeight = ();
	type BlockExecutionWeight = ();
	type ExtrinsicBaseWeight = ();
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

type Extrinsic = TestXt<Call<Test>, ()>;
type AccountId = <<Signature as Verify>::Signer as IdentifyAccount>::AccountId;

impl frame_system::offchain::SigningTypes for Test {
	type Public = <Signature as Verify>::Signer;
	type Signature = Signature;
}

impl<LocalCall> frame_system::offchain::SendTransactionTypes<LocalCall> for Test where
	Call<Test>: From<LocalCall>,
{
	type OverarchingCall = Call<Test>;
	type Extrinsic = Extrinsic;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Test where
	Call<Test>: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call<Test>,
		_public: <Signature as Verify>::Signer,
		_account: AccountId,
		nonce: u64,
	) -> Option<(Call<Test>, <Extrinsic as ExtrinsicT>::SignaturePayload)> {
		Some((call, (nonce, ())))
	}
}

parameter_types! {
	pub const GracePeriod: u64 = 5;
	pub const UnsignedInterval: u64 = 128;
	pub const UnsignedPriority: u64 = 1 << 20;
}

impl Trait for Test {
	type Event = ();
	type AuthorityId = crypto::TestAuthId;
	type Call = Call<Test>;
	type GracePeriod = GracePeriod;
	type UnsignedInterval = UnsignedInterval;
	type UnsignedPriority = UnsignedPriority;
}

type Example = Module<Test>;

#[test]
fn it_aggregates_the_price() {
	sp_io::TestExternalities::default().execute_with(|| {
		assert_eq!(Example::average_price(), None);

		assert_ok!(Example::submit_price(Origin::signed(Default::default()), 27));
		assert_eq!(Example::average_price(), Some(27));

		assert_ok!(Example::submit_price(Origin::signed(Default::default()), 43));
		assert_eq!(Example::average_price(), Some(35));
	});
}

#[test]
fn should_make_http_call_and_parse_result() {
	let (offchain, state) = testing::TestOffchainExt::new();
	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));

	price_oracle_response(&mut state.write());

	t.execute_with(|| {
		// when
		let price = Example::fetch_price().unwrap();
		// then
		assert_eq!(price, 15523);
	});
}

#[test]
fn should_submit_signed_transaction_on_chain() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";

	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = KeyStore::new();
	keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();


	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore));

	price_oracle_response(&mut offchain_state.write());

	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_signed().unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature.unwrap().0, 0);
		assert_eq!(tx.call, Call::submit_price(15523));
	});
}

#[test]
fn should_submit_unsigned_transaction_on_chain_for_any_account() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	price_oracle_response(&mut offchain_state.write());

	let public_key = keystore.read()
		.sr25519_public_keys(crate::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	let price_payload = PricePayload {
		block_number: 1,
		price: 15523,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	// let signature = price_payload.sign::<crypto::TestAuthId>().unwrap();
	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_unsigned_for_any_account(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let Call::submit_price_unsigned_with_signed_payload(body, signature) = tx.call {
			assert_eq!(body, price_payload);

			let signature_valid = <PricePayload<
				<Test as SigningTypes>::Public,
				<Test as frame_system::Trait>::BlockNumber
					> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&price_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_unsigned_transaction_on_chain_for_all_accounts() {
	const PHRASE: &str = "news slush supreme milk chapter athlete soap sausage put clutch what kitten";
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", PHRASE))
	).unwrap();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore.clone()));

	price_oracle_response(&mut offchain_state.write());

	let public_key = keystore.read()
		.sr25519_public_keys(crate::crypto::Public::ID)
		.get(0)
		.unwrap()
		.clone();

	let price_payload = PricePayload {
		block_number: 1,
		price: 15523,
		public: <Test as SigningTypes>::Public::from(public_key),
	};

	// let signature = price_payload.sign::<crypto::TestAuthId>().unwrap();
	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_unsigned_for_all_accounts(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		if let Call::submit_price_unsigned_with_signed_payload(body, signature) = tx.call {
			assert_eq!(body, price_payload);

			let signature_valid = <PricePayload<
				<Test as SigningTypes>::Public,
				<Test as frame_system::Trait>::BlockNumber
					> as SignedPayload<Test>>::verify::<crypto::TestAuthId>(&price_payload, signature);

			assert!(signature_valid);
		}
	});
}

#[test]
fn should_submit_raw_unsigned_transaction_on_chain() {
	let (offchain, offchain_state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();

	let keystore = KeyStore::new();

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore));

	price_oracle_response(&mut offchain_state.write());

	t.execute_with(|| {
		// when
		Example::fetch_price_and_send_raw_unsigned(1).unwrap();
		// then
		let tx = pool_state.write().transactions.pop().unwrap();
		assert!(pool_state.read().transactions.is_empty());
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.signature, None);
		assert_eq!(tx.call, Call::submit_price_unsigned(1, 15523));
	});
}

fn price_oracle_response(state: &mut testing::OffchainState) {
	state.expect_request(0, testing::PendingRequest {
		method: "GET".into(),
		uri: "https://min-api.cryptocompare.com/data/price?fsym=BTC&tsyms=USD".into(),
		response: Some(br#"{"USD": 155.23}"#.to_vec()),
		sent: true,
		..Default::default()
	});
}

#[test]
fn parse_price_works() {
	let test_data = vec![
		("{\"USD\":6536.92}", Some(653692)),
		("{\"USD\":65.92}", Some(6592)),
		("{\"USD\":6536.924565}", Some(653692)),
		("{\"USD\":6536}", Some(653600)),
		("{\"USD2\":6536}", None),
		("{\"USD\":\"6432\"}", None),
	];

	for (json, expected) in test_data {
		assert_eq!(expected, Example::parse_price(json));
	}
}
