use super::*;
use crate as pallet_timestamp;

use frame_support::{
    assert_ok, parameter_types,
    traits::{ConstU32, ConstU64},
};
use sp_core::H256;
use sp_io::TestExternalities;
use sp_runtime::{
    testing::Header,
    traits::{BlakeTwo256, IdentityLookup},
};

pub fn new_test_ext() -> TestExternalities {
    let t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
    TestExternalities::new(t)
}

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
			Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		}
	);

parameter_types! {
		pub BlockWeights: frame_system::limits::BlockWeights =
			frame_system::limits::BlockWeights::simple_max(1024);
	}
impl frame_system::Config for Test {
    type BaseCallFilter = frame_support::traits::Everything;
    type BlockWeights = ();
    type BlockLength = ();
    type DbWeight = ();
    type Origin = Origin;
    type Index = u64;
    type BlockNumber = u64;
    type Call = Call;
    type Hash = H256;
    type Hashing = BlakeTwo256;
    type AccountId = u64;
    type Lookup = IdentityLookup<Self::AccountId>;
    type Header = Header;
    type Event = Event;
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

impl Config for Test {
    type Moment = u64;
    type OnTimestampSet = ();
    type MinimumPeriod = ConstU64<5>;
    type WeightInfo = ();
}

#[test]
fn timestamp_works() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        assert_ok!(Timestamp::set(Origin::none(), 69));
        assert_eq!(Timestamp::now(), 69);
    });
}

#[test]
#[should_panic(expected = "Timestamp must be updated only once in the block")]
fn double_timestamp_should_fail() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        assert_ok!(Timestamp::set(Origin::none(), 69));
        let _ = Timestamp::set(Origin::none(), 70);
    });
}

#[test]
#[should_panic(
expected = "Timestamp must increment by at least <MinimumPeriod> between sequential blocks"
)]
fn block_period_minimum_enforced() {
    new_test_ext().execute_with(|| {
        Timestamp::set_timestamp(42);
        let _ = Timestamp::set(Origin::none(), 46);
    });
}