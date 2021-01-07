#![cfg(test)]

use super::*;

use frame_support::{impl_outer_origin, parameter_types};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

impl_outer_origin! {
	pub enum Origin for Test where system = frame_system {}
}

#[derive(Clone, Eq, Debug, PartialEq)]
pub struct Test;
parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);
}
impl frame_system::Config for Test {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
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
	type Version = ();
	type PalletInfo = ();
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
}
parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}
impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type Balance = u64;
	type DustRemoval = ();
	type Event = ();
	type ExistentialDeposit = ExistentialDeposit;
	type AccountStore = System;
	type WeightInfo = ();
}
parameter_types! {
	pub const ProofLimit: u32 = 1024;
	pub const ExpireDuration: u64 = 100;
}
impl Config for Test {
	type Event = ();
	type SwapAction = BalanceSwapAction<u64, Balances>;
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
