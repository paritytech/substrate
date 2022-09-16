#![cfg(test)]

use super::*;

use frame_support::{ord_parameter_types, parameter_types, weights::Weight};
use frame_system::{self as system};
use sp_core::hashing::blake2_128;
use sp_core::H256;
use sp_runtime::{
    testing::Header,
    traits::{AccountIdConversion, BlakeTwo256, Block as BlockT, IdentityLookup},
    Perbill,
};

use crate::{self as example, Trait};
use chainbridge as bridge;
pub use pallet_balances as balances;

parameter_types! {
    pub const BlockHashCount: u64 = 250;
    pub const MaximumBlockWeight: Weight = 1024;
    pub const MaximumBlockLength: u32 = 2 * 1024;
    pub const AvailableBlockRatio: Perbill = Perbill::one();
}

impl frame_system::Trait for Test {
    type BaseCallFilter = ();
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
    type MaximumBlockWeight = MaximumBlockWeight;
    type DbWeight = ();
    type BlockExecutionWeight = ();
    type ExtrinsicBaseWeight = ();
    type MaximumExtrinsicWeight = ();
    type MaximumBlockLength = MaximumBlockLength;
    type AvailableBlockRatio = AvailableBlockRatio;
    type Version = ();
    type ModuleToIndex = ();
    type AccountData = balances::AccountData<u64>;
    type OnNewAccount = ();
    type OnKilledAccount = ();
    type SystemWeightInfo = ();
}

parameter_types! {
    pub const ExistentialDeposit: u64 = 1;
}

ord_parameter_types! {
    pub const One: u64 = 1;
}

impl pallet_balances::Trait for Test {
    type Balance = u64;
    type DustRemoval = ();
    type Event = Event;
    type ExistentialDeposit = ExistentialDeposit;
    type AccountStore = System;
    type WeightInfo = ();
}

parameter_types! {
    pub const TestChainId: u8 = 5;
    pub const ProposalLifetime: u64 = 100;
}

impl bridge::Trait for Test {
    type Event = Event;
    type AdminOrigin = frame_system::EnsureRoot<Self::AccountId>;
    type Proposal = Call;
    type ChainId = TestChainId;
    type ProposalLifetime = ProposalLifetime;
}

parameter_types! {
    pub HashId: bridge::ResourceId = bridge::derive_resource_id(1, &blake2_128(b"hash"));
    pub NativeTokenId: bridge::ResourceId = bridge::derive_resource_id(1, &blake2_128(b"DAV"));
    pub Erc721Id: bridge::ResourceId = bridge::derive_resource_id(1, &blake2_128(b"NFT"));
}

impl erc721::Trait for Test {
    type Event = Event;
    type Identifier = Erc721Id;
}

impl Trait for Test {
    type Event = Event;
    type BridgeOrigin = bridge::EnsureBridge<Test>;
    type Currency = Balances;
    type HashId = HashId;
    type NativeTokenId = NativeTokenId;
    type Erc721Id = Erc721Id;
}

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

frame_support::construct_runtime!(
    pub enum Test where
        Block = Block,
        NodeBlock = Block,
        UncheckedExtrinsic = UncheckedExtrinsic
    {
        System: system::{Pallet, Call, Event<T>},
        Balances: balances::{Pallet, Call, Storage, Config<T>, Event<T>},
        Bridge: bridge::{Pallet, Call, Storage, Event<T>},
        Erc721: erc721::{Pallet, Call, Storage, Event<T>},
        Example: example::{Pallet, Call, Event<T>}
    }
);

pub const RELAYER_A: u64 = 0x2;
pub const RELAYER_B: u64 = 0x3;
pub const RELAYER_C: u64 = 0x4;
pub const ENDOWED_BALANCE: u64 = 100_000_000;

pub fn new_test_ext() -> sp_io::TestExternalities {
    let bridge_id = PalletId(*b"cb/bridg").into_account();
    let mut t = frame_system::GenesisConfig::default()
        .build_storage::<Test>()
        .unwrap();
    pallet_balances::GenesisConfig::<Test> {
        balances: vec![(bridge_id, ENDOWED_BALANCE), (RELAYER_A, ENDOWED_BALANCE)],
    }
    .assimilate_storage(&mut t)
    .unwrap();
    let mut ext = sp_io::TestExternalities::new(t);
    ext.execute_with(|| System::set_block_number(1));
    ext
}

fn last_event() -> Event {
    system::Module::<Test>::events()
        .pop()
        .map(|e| e.event)
        .expect("Event expected")
}

pub fn expect_event<E: Into<Event>>(e: E) {
    assert_eq!(last_event(), e.into());
}

// Asserts that the event was emitted at some point.
pub fn event_exists<E: Into<Event>>(e: E) {
    let actual: Vec<Event> = system::Module::<Test>::events()
        .iter()
        .map(|e| e.event.clone())
        .collect();
    let e: Event = e.into();
    let mut exists = false;
    for evt in actual {
        if evt == e {
            exists = true;
            break;
        }
    }
    assert!(exists);
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
        assert_eq!(next, evt.into(), "Events don't match");
    }
}
