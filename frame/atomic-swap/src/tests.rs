#![cfg(test)]

use super::*;

use frame_support::{
	impl_outer_origin, parameter_types, weights::Weight,
};
use sp_core::H256;
// The testing primitives are very useful for avoiding having to work with signatures
// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
use sp_runtime::{
	Perbill,
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

// For testing the pallet, we construct most of a mock runtime. This means
// first constructing a configuration type (`Test`) which `impl`s each of the
// configuration traits of pallets we want to use.
#[derive(Clone, Eq, Debug, PartialEq)]
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
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Call = ();
	type Hashing = BlakeTwo256;
	type AccountId = u64;
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
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Trait for Test {
	type Balance = u64;
	type DustRemoval = ();
	type Event = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
}
parameter_types! {
	pub const ProofLimit: u32 = 1024;
	pub const ExpireDuration: u64 = 100;
}
impl Trait for Test {
	type Event = ();
	type SwapAction = BalanceSwapAction<Test, Balances>;
	type ProofLimit = ProofLimit;
}
type System = frame_system::Module<Test>;
type Balances = pallet_balances::Module<Test>;
type AtomicSwap = Module<Test>;

const A: u64 = 1;
const B: u64 = 2;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let genesis = pallet_balances::GenesisConfig::<Test> {
		balances: vec![
			(A, 100),
			(B, 200),
		],
	};
	genesis.assimilate_storage(&mut t).unwrap();
	t.into()
}

#[test]
fn two_party_successful_swap() {
	let mut chain1 = new_test_ext();
	let mut chain2 = new_test_ext();

	// A generates a random proof. Keep it secret.
	let proof: [u8; 2] = [4, 2];
	// The hashed proof is the blake2_256 hash of the proof. This is public.
	let hashed_proof = blake2_256(&proof);

	// A creates the swap on chain1.
	chain1.execute_with(|| {
		AtomicSwap::create_swap(
			Origin::signed(A),
			B,
			hashed_proof.clone(),
			BalanceSwapAction::new(50),
			1000,
		).unwrap();

		assert_eq!(Balances::free_balance(A), 100 - 50);
		assert_eq!(Balances::free_balance(B), 200);
	});

	// B creates the swap on chain2.
	chain2.execute_with(|| {
		AtomicSwap::create_swap(
			Origin::signed(B),
			A,
			hashed_proof.clone(),
			BalanceSwapAction::new(75),
			1000,
		).unwrap();

		assert_eq!(Balances::free_balance(A), 100);
		assert_eq!(Balances::free_balance(B), 200 - 75);
	});

	// A reveals the proof and claims the swap on chain2.
	chain2.execute_with(|| {
		AtomicSwap::claim_swap(
			Origin::signed(A),
			proof.to_vec(),
			BalanceSwapAction::new(75),
		).unwrap();

		assert_eq!(Balances::free_balance(A), 100 + 75);
		assert_eq!(Balances::free_balance(B), 200 - 75);
	});

	// B use the revealed proof to claim the swap on chain1.
	chain1.execute_with(|| {
		AtomicSwap::claim_swap(
			Origin::signed(B),
			proof.to_vec(),
			BalanceSwapAction::new(50),
		).unwrap();

		assert_eq!(Balances::free_balance(A), 100 - 50);
		assert_eq!(Balances::free_balance(B), 200 + 50);
	});
}
