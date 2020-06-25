// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use crate::*;

use codec::{Encode, Decode};
use frame_support::{
	impl_outer_origin, parameter_types,
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
	type BaseCallFilter = ();
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
	type MaximumExtrinsicWeight = MaximumBlockWeight;
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

impl Trait for Test {
	type Event = ();
	type AuthorityId = crypto::TestAuthId;
	type Call = Call<Test>;
}

type SgxTest = Module<Test>;

fn setup_enclave_and_ias_responses(state: &mut testing::OffchainState) {
	let fetch_quote_from_enclave = testing::PendingRequest {
		method: "POST".into(),
		uri: "https://myenclave_runs_here.example.com/quoting_report".into(),
		response: Some(br#"123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here 123 whatever goes here "#.to_vec()),
		sent: true,
		body: b"remote_attest\r\n".to_vec(),
		headers: vec![("substrate_sgx".into(), "1.0".into())],
		..Default::default()
	};
	let send_quote_to_intel = testing::PendingRequest {
		method: "POST".into(),
		uri: "https://api.trustedservices.intel.com/sgx/dev/attestation/v4/report".into(),
		headers: vec![("Content-Type".into(), "application/json".into()), ("Ocp-Apim-Subscription-Key".into(), "e9589de0dfe5482588600a73d08b70f6".into())],
		response: Some(br#"Response from Intel goes here"#.to_vec()),
		sent: true,
		body: vec![123, 34, 105, 115, 118, 69, 110, 99, 108, 97, 118, 101, 81, 117, 111, 116, 101, 34, 58, 34, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 68, 69, 121, 77, 121, 66, 51, 97, 71, 70, 48, 90, 88, 90, 108, 99, 105, 66, 110, 98, 50, 86, 122, 73, 71, 104, 108, 99, 109, 85, 103, 77, 84, 73, 122, 73, 72, 100, 111, 89, 88, 82, 108, 100, 109, 86, 121, 73, 71, 100, 118, 90, 88, 77, 103, 97, 71, 86, 121, 90, 83, 65, 120, 77, 106, 77, 103, 100, 50, 104, 104, 100, 71, 86, 50, 90, 88, 73, 103, 90, 50, 57, 108, 99, 121, 66, 111, 90, 88, 74, 108, 73, 65, 61, 61, 34, 125],
		..Default::default()
	};
	state.expect_request(0, fetch_quote_from_enclave);
	state.expect_request(1, send_quote_to_intel);
}

#[test]
fn registers_a_valid_enclave_on_chain() {
	env_logger::init();
	let (offchain, state) = testing::TestOffchainExt::new();
	let (pool, pool_state) = testing::TestTransactionPoolExt::new();
	let keystore = KeyStore::new();

	let pk = keystore.write().sr25519_generate_new(
		crate::crypto::Public::ID,
		Some(&format!("{}/hunter1", "news slush supreme milk chapter athlete soap sausage put clutch what kitten"))
	).expect("can generate new keypair");

	let mut t = sp_io::TestExternalities::default();
	t.register_extension(OffchainExt::new(offchain));
	t.register_extension(TransactionPoolExt::new(pool));
	t.register_extension(KeystoreExt(keystore));

	let expected_enclave = Enclave {
		quote: QuotingReport {
			cpusvn: [51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32],
			miscselect: 1701995880,
			attributes: [119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32, 104, 101],
			mrenclave: [114, 101, 32, 49, 50, 51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32, 104, 101, 114, 101, 32, 49, 50, 51, 32, 119, 104],
			mrsigner: [101, 115, 32, 104, 101, 114, 101, 32, 49, 50, 51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32, 104, 101, 114, 101, 32, 49],
			isvprodid: 24936,
			isvsvn: 25972,
			reportdata: vec![49, 50, 51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32, 104, 101, 114, 101, 32, 49, 50, 51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32, 104, 101, 114, 101, 32, 49, 50, 51, 32, 119, 104, 97, 116, 101, 118, 101, 114, 32, 103, 111, 101, 115, 32] },
			address: br#"https://myenclave_runs_here.example.com"#.to_vec(),
			timestamp: 0
		};

	// Mock http calls to the enclave and IAS
	setup_enclave_and_ias_responses(&mut state.write());

	t.execute_with(|| {
		SgxTest::register_enclave(
			Origin::signed(pk),
			br#"https://myenclave_runs_here.example.com"#.to_vec()
		).expect("not under test, expected to work here");

		// makes two http calls: get a QUOTE from the enclave and send the QUOTE to Intel for RA
		SgxTest::remote_attest_unverified_enclaves().unwrap();

		let tx = pool_state.write().transactions.pop().unwrap();
		let tx = Extrinsic::decode(&mut &*tx).unwrap();
		assert_eq!(tx.call, Call::register_verified_enclave(pk, expected_enclave));
	});
}
