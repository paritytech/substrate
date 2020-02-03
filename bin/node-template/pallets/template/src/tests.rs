// Tests to be written here
#![cfg(test)]

use crate::{Module, Trait, Error};
use sp_core::H256;
use frame_support::{impl_outer_origin, assert_ok, assert_noop, parameter_types, weights::Weight};
use sp_runtime::{
	traits::{BlakeTwo256, IdentityLookup}, testing::Header, Perbill,
};

impl_outer_origin! {
	pub enum Origin for Test {}
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
	pub const AvailableBlockRatio: Perbill = Perbill::from_percent(75);
}
impl system::Trait for Test {
	type Origin = Origin;
	type Call = ();
	type Index = u64;
	type BlockNumber = u64;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type AccountId = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = ();
	type BlockHashCount = BlockHashCount;
	type MaximumBlockWeight = MaximumBlockWeight;
	type MaximumBlockLength = MaximumBlockLength;
	type AvailableBlockRatio = AvailableBlockRatio;
	type Version = ();
	type ModuleToIndex = ();
}
impl Trait for Test {
	type Event = ();
}
type TemplateModule = Module<Test>;

// This function basically just builds a genesis storage key/value store according to
// our desired mockup.
fn new_test_ext() -> sp_io::TestExternalities {
	system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}

#[test]
fn it_works_for_default_value() {
	new_test_ext().execute_with(|| {
		// Just a dummy test for the dummy funtion `do_something`
		// calling the `do_something` function with a value 42
		assert_ok!(TemplateModule::do_something(Origin::signed(1), 42));
		// asserting that the stored value is equal to what we stored
		assert_eq!(TemplateModule::something(), Some(42));
	});
}

#[test]
fn correct_error_for_none_value() {
	new_test_ext().execute_with(|| {
		// Ensure the correct error is thrown on None value
		assert_noop!(
			TemplateModule::cause_error(Origin::signed(1)),
			Error::<Test>::NoneValue
		);
	});
}
