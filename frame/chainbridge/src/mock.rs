#![cfg(test)]

use super::*;

use frame_support::{assert_ok, ord_parameter_types, parameter_types, weights::Weight, PalletId};
use frame_system::{self as system};
use sp_core::H256;
use sp_runtime::{
    testing::Header,
    traits::{AccountIdConversion, BlakeTwo256, Block as BlockT, IdentityLookup},
    Perbill,
};

use crate::{self as bridge, Config};
pub use pallet_balances as balances;

parameter_types! {
    pub const BlockHashCount: u64 = 250;
    pub const MaximumBlockWeight: Weight = 1024;
    pub const MaximumBlockLength: u32 = 2 * 1024;
    pub const AvailableBlockRatio: Perbill = Perbill::one();
    pub const MaxLocks: u32 = 50;
}

impl frame_system::Config for Test {
    type BaseCallFilter = ();
    type BlockWeights = ();
    type BlockLength = ();
    type Origin = Origin;
    type Call = Call;
    type Index = u64;
    type BlockNumber = u64;
    type Hash = H256;
    type Hashing = BlakeTwo256;
    type AccountId = u64;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = Header;
    type Event = Event;
    type BlockHashCount = BlockHashCount;
    type DbWeight = ();
    type Version = ();
    // type ModuleToIndex = ();
    type PalletInfo = PalletInfo;
    // type MaxLocks = MaxLocks;
    type AccountData = pallet_balances::AccountData<u64>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
    type SS58Prefix = ();
    type OnSetCode = ();
}

parameter_types! {
    pub const ExistentialDeposit: u64 = 1;
}

ord_parameter_types! {
    pub const One: u64 = 1;
}

impl pallet_balances::Config for Test {
    type Balance = u64;
    type DustRemoval = ();
    type Event = Event;
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
    type MaxLocks = ();
    type MaxReserves = ();
    type ReserveIdentifier = ();
}

parameter_types! {
    pub const TestChainId: u8 = 5;
    pub const ProposalLifetime: u64 = 50;
}

impl Config for Test {
    type Event = Event;
    type AdminOrigin = frame_system::EnsureRoot<Self::AccountId>;
    type Proposal = Call;
    type ChainId = TestChainId;
    type ProposalLifetime = ProposalLifetime;
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
    pub enum Test where
        Block = Block,
        NodeBlock = Block,
        UncheckedExtrinsic = UncheckedExtrinsic
    {
        System: system::{Pallet, Call, Event<T>},
        Balances: balances::{Pallet, Call, Storage, Config<T>, Event<T>},
        Bridge: bridge::{Pallet, Call, Storage, Event<T>},
    }
);

// pub const BRIDGE_ID: u64 =
pub const RELAYER_A: u64 = 0x2;
pub const RELAYER_B: u64 = 0x3;
pub const RELAYER_C: u64 = 0x4;
pub const ENDOWED_BALANCE: u64 = 100_000_000;
pub const TEST_THRESHOLD: u32 = 2;

pub fn new_test_ext() -> sp_io::TestExternalities {
    let bridge_id = PalletId(*b"cb/bridg").into_account();
    let mut t = frame_system::GenesisConfig::default()
        .build_storage::<Test>()
        .unwrap();
    pallet_balances::GenesisConfig::<Test> {
        balances: vec![(bridge_id, ENDOWED_BALANCE)],
    }
    .assimilate_storage(&mut t)
    .unwrap();
    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| System::set_block_number(1));
    ext
}

pub fn new_test_ext_initialized(
    src_id: ChainId,
    r_id: ResourceId,
    resource: Vec<u8>,
) -> sp_io::TestExternalities {
    let mut t = new_test_ext();
    t.execute_with(|| {
        // Set and check threshold
        assert_ok!(Bridge::set_threshold(Origin::root(), TEST_THRESHOLD));
        assert_eq!(Bridge::relayer_threshold(), TEST_THRESHOLD);
        // Add relayers
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_A));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_B));
        assert_ok!(Bridge::add_relayer(Origin::root(), RELAYER_C));
        // Whitelist chain
        assert_ok!(Bridge::whitelist_chain(Origin::root(), src_id));
        // Set and check resource ID mapped to some junk data
        assert_ok!(Bridge::set_resource(Origin::root(), r_id, resource));
        assert_eq!(Bridge::resource_exists(r_id), true);
    });
    t
}

// Checks events against the latest. A contiguous set of events must be provided. They must
// include the most recent event, but do not have to include every past event.
pub fn assert_events(mut expected: Vec<Event>) {
    let mut actual: Vec<Event> = system::Module::<Test>::events()
        .iter()
        .map(|e| e.event.clone())
        .collect();

    expected.reverse();

    for evt in expected {
        let next = actual.pop().expect("event expected");
        assert_eq!(next, evt.into(), "Events don't match (actual,expected)");
    }
}
