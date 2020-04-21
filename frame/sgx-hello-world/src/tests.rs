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

use codec::Decode;
use frame_support::{
	assert_ok, impl_outer_origin, parameter_types,
	weights::Weight,
};
use sp_core::{
	H256,
	offchain::{OffchainExt, TransactionPoolExt, testing},
	testing::KeyStore,
	traits::KeystoreExt,
};
use sp_runtime::{
	Perbill, RuntimeAppPublic,
	testing::{Header, TestXt},
	traits::{BlakeTwo256, IdentityLookup, Extrinsic as ExtrinsicsT},
};

impl_outer_origin! {
	pub enum Origin for Test  where system = frame_system {}
}

// For testing the module, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of modules we want to use.
#[derive(Clone, Eq, PartialEq)]
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
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
}

type Extrinsic = TestXt<Call<Test>, ()>;
type SubmitTransaction = frame_system::offchain::TransactionSubmitter<
	crypto::Public,
	Test,
	Extrinsic
>;

impl frame_system::offchain::CreateTransaction<Test, Extrinsic> for Test {
	type Public = sp_core::sr25519::Public;
	type Signature = sp_core::sr25519::Signature;

	fn create_transaction<F: frame_system::offchain::Signer<Self::Public, Self::Signature>>(
		call: <Extrinsic as ExtrinsicsT>::Call,
		_public: Self::Public,
		_account: <Test as frame_system::Trait>::AccountId,
		nonce: <Test as frame_system::Trait>::Index,
	) -> Option<(<Extrinsic as ExtrinsicsT>::Call, <Extrinsic as ExtrinsicsT>::SignaturePayload)> {
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
	type Call = Call<Test>;
	type SubmitSignedTransaction = SubmitTransaction;
	type SubmitUnsignedTransaction = SubmitTransaction;
	type GracePeriod = GracePeriod;
	type UnsignedInterval = UnsignedInterval;
	type UnsignedPriority = UnsignedPriority;
}

type Example = Module<Test>;
