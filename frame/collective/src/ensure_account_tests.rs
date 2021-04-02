use super::*;
use frame_support::parameter_types;
use frame_system::{self as system};
use sp_core::H256;
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup}, testing::Header,
};
use crate as collective;

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const MotionDuration: u64 = 3;
	pub const MaxProposals: u32 = 100;
	pub const MaxMembers: u32 = 100;
	pub const CollectiveModuleId0: ModuleId = ModuleId(*b"py/coll0");
	pub const CollectiveModuleId1: ModuleId = ModuleId(*b"py/coll1");
	pub const CollectiveModuleId2: ModuleId = ModuleId(*b"py/coll2");
	pub BlockWeights: frame_system::limits::BlockWeights =
		frame_system::limits::BlockWeights::simple_max(1024);

}

// Need a new runtime test environment where Account ID is bigger than u64
use sp_runtime::AccountId32;
impl frame_system::Config for AccountTest {
	type BaseCallFilter = ();
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u64;
	type Call = Call;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = AccountId32;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = BlockHashCount;
	type Version = ();
	type PalletInfo = PalletInfo;
	type AccountData = ();
	type OnNewAccount = ();
	type OnKilledAccount = ();
	type SystemWeightInfo = ();
	type SS58Prefix = ();
	type OnSetCode = ();
}
impl Config<Instance2> for AccountTest {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type ModuleId = CollectiveModuleId2;
	type WeightInfo = ();
}
impl Config for AccountTest {
	type Origin = Origin;
	type Proposal = Call;
	type Event = Event;
	type MotionDuration = MotionDuration;
	type MaxProposals = MaxProposals;
	type MaxMembers = MaxMembers;
	type DefaultVote = PrimeDefaultVote;
	type ModuleId = CollectiveModuleId0;
	type WeightInfo = ();
}

pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, u64, Call, ()>;

frame_support::construct_runtime!(
	pub enum AccountTest where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Call, Event<T>},
		Collective: collective::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
		Collective2: collective::<Instance2>::{Pallet, Call, Event<T>, Origin<T>, Config<T>},
	}
);

#[test]
fn ensure_more_than_accounts_work() {
	use sp_core::u32_trait::{_1, _2, _3};
	type MoreThanHalf = EnsureProportionMoreThanToAccount<_1, _2, AccountTest>;
	type MoreThanTwoThirds = EnsureProportionMoreThanToAccount<_2, _3, AccountTest>;

	let one_half = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(1u32, 2u32));
	let two_thirds = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(2u32, 3u32));
	let three_fourths = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(3u32, 4u32));

	// 1/2 is not more than 1/2
	assert!(MoreThanHalf::ensure_origin(one_half).is_err());
	// 2/3 and 3/4 are.
	let two_thirds_account = MoreThanHalf::ensure_origin(two_thirds).unwrap();
	let three_fourths_account = MoreThanHalf::ensure_origin(three_fourths.clone()).unwrap();

	// Both origins should produce the same account, which represents more than 1/2
	assert_eq!(two_thirds_account, three_fourths_account);

	// These two accounts should not be equal because they do not represent the same proportion.
	let three_fourths_account_2_3 = MoreThanTwoThirds::ensure_origin(three_fourths).unwrap();
	assert!(three_fourths_account != three_fourths_account_2_3);

	// Two instances should also have different account ids
	type MoreThanHalfI2 = EnsureProportionMoreThanToAccount<_1, _2, AccountTest, Instance2>;
	let three_fourths_i2 = Origin::from(RawOrigin::<AccountId32, Instance2>::Members(3u32, 4u32));
	let three_fourths_account_i2 = MoreThanHalfI2::ensure_origin(three_fourths_i2).unwrap();

	// Accounts should be different
	assert!(three_fourths_account != three_fourths_account_i2);
}

#[test]
fn ensure_at_least_accounts_work() {
	use sp_core::u32_trait::{_1, _2, _3};
	type AtLeastHalf = EnsureProportionAtLeastToAccount<_1, _2, AccountTest>;
	type AtLeastTwoThirds = EnsureProportionAtLeastToAccount<_2, _3, AccountTest>;

	let one_third = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(1u32, 3u32));
	let one_half = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(1u32, 2u32));
	let three_fourths = Origin::from(RawOrigin::<AccountId32, DefaultInstance>::Members(3u32, 4u32));

	// 1/3 is not at least 1/2
	assert!(AtLeastHalf::ensure_origin(one_third).is_err());
	// 1/2 and 3/4 are.
	let one_half_account = AtLeastHalf::ensure_origin(one_half).unwrap();
	let three_fourths_account = AtLeastHalf::ensure_origin(three_fourths.clone()).unwrap();

	// Both origins should produce the same account, which represents more than 1/2
	assert_eq!(one_half_account, three_fourths_account);

	// These two accounts should not be equal because they do not represent the same proportion.
	let three_fourths_account_2_3 = AtLeastTwoThirds::ensure_origin(three_fourths).unwrap();
	assert!(three_fourths_account != three_fourths_account_2_3);

	// Two instances should also have different account ids
	type AtLeastHalfI2 = EnsureProportionAtLeastToAccount<_1, _2, AccountTest, Instance2>;
	let three_fourths_i2 = Origin::from(RawOrigin::<AccountId32, Instance2>::Members(3u32, 4u32));
	let three_fourths_account_i2 = AtLeastHalfI2::ensure_origin(three_fourths_i2).unwrap();

	// Accounts should be different
	assert!(three_fourths_account != three_fourths_account_i2);
}
