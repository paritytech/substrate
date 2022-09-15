#![cfg(test)]

use super::*;
use crate as pallet_atomic_swap;

use frame_support::{
	parameter_types,
	traits::{ConstU32, ConstU64},
};
use sp_core::H256;
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		AtomicSwap: pallet_atomic_swap::{Pallet, Call, Event<T>},
	}
);

parameter_types! {
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(frame_support::weights::Weight::from_ref_time(1024));
}
impl frame_system::Config for Test {
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type RuntimeCall = RuntimeCall;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU64<250>;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = pallet_balances::AccountData<u64>;
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

impl pallet_balances::Config for Test {
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type Balance = u64;
	type DustRemoval = ();
	type RuntimeEvent = RuntimeEvent;
	type ExistentialDeposit = ConstU64<1>;
	type AccountStore = System;
	type WeightInfo = ();
}

impl Config for Test {
	type RuntimeEvent = RuntimeEvent;
	type SwapAction = BalanceSwapAction<u64, Balances>;
	type ProofLimit = ConstU32<1024>;
}

const A: u64 = 1;
const B: u64 = 2;

pub fn new_test_ext() -> sp_io::TestExternalities {
	let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
	let genesis = pallet_balances::GenesisConfig::<Test> { balances: vec![(A, 100), (B, 200)] };
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
			hashed_proof,
			BalanceSwapAction::new(50),
			1000,
		)
		.unwrap();

		assert_eq!(Balances::free_balance(A), 100 - 50);
		assert_eq!(Balances::free_balance(B), 200);
	});

	// B creates the swap on chain2.
	chain2.execute_with(|| {
		AtomicSwap::create_swap(
			Origin::signed(B),
			A,
			hashed_proof,
			BalanceSwapAction::new(75),
			1000,
		)
		.unwrap();

		assert_eq!(Balances::free_balance(A), 100);
		assert_eq!(Balances::free_balance(B), 200 - 75);
	});

	// A reveals the proof and claims the swap on chain2.
	chain2.execute_with(|| {
		AtomicSwap::claim_swap(Origin::signed(A), proof.to_vec(), BalanceSwapAction::new(75))
			.unwrap();

		assert_eq!(Balances::free_balance(A), 100 + 75);
		assert_eq!(Balances::free_balance(B), 200 - 75);
	});

	// B use the revealed proof to claim the swap on chain1.
	chain1.execute_with(|| {
		AtomicSwap::claim_swap(Origin::signed(B), proof.to_vec(), BalanceSwapAction::new(50))
			.unwrap();

		assert_eq!(Balances::free_balance(A), 100 - 50);
		assert_eq!(Balances::free_balance(B), 200 + 50);
	});
}
