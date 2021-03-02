#![cfg(test)]

mod tests {
	use super::*;

	use frame_support::{
		assert_ok, parameter_types,
		weights::{DispatchInfo, GetDispatchInfo}, traits::{OnInitialize, OnFinalize}
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{
		testing::Header, BuildStorage,
		traits::{BlakeTwo256, IdentityLookup},
	};
	// Reexport crate as its pallet name for construct_runtime.
	use crate as pallet_example;

	type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
	type Block = frame_system::mocking::MockBlock<Test>;

	// For testing the pallet, we construct a mock runtime.
	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Module, Call, Config, Storage, Event<T>},
			Balances: pallet_balances::{Module, Call, Storage, Config<T>, Event<T>},
			Example: pallet_example::{Module, Call, Storage, Config<T>, Event<T>},
		}
	);

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
		type Call = Call;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = Event;
		type BlockHashCount = BlockHashCount;
		type Version = ();
		type PalletInfo = PalletInfo;
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
		type Event = Event;
		type ExistentialDeposit = ExistentialDeposit;
		type AccountStore = System;
		type WeightInfo = ();
	}
	impl Config for Test {
		type Event = Event;
	}

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	pub fn new_test_ext() -> sp_io::TestExternalities {
		let t = GenesisConfig {
			// We use default for brevity, but you can configure as desired if needed.
			frame_system: Some(Default::default()),
			pallet_balances: Some(Default::default()),
			pallet_example: Some(pallet_example::GenesisConfig {
				dummy: 42,
				// we configure the map with (key, value) pairs.
				bar: vec![(1, 2), (2, 3)],
				foo: 24,
			}),
		}.build_storage().unwrap();
		t.into()
	}

	#[test]
	fn it_works_for_optional_value() {
		new_test_ext().execute_with(|| {
			// Check that GenesisBuilder works properly.
			assert_eq!(Example::dummy(), Some(42));

			// Check that accumulate works when we have Some value in Dummy already.
			assert_ok!(Example::accumulate_dummy(Origin::signed(1), 27));
			assert_eq!(Example::dummy(), Some(69));

			// Check that finalizing the block removes Dummy from storage.
			<Example as OnFinalize<u64>>::on_finalize(1);
			assert_eq!(Example::dummy(), None);

			// Check that accumulate works when we Dummy has None in it.
			<Example as OnInitialize<u64>>::on_initialize(2);
			assert_ok!(Example::accumulate_dummy(Origin::signed(1), 42));
			assert_eq!(Example::dummy(), Some(42));
		});
	}

	#[test]
	fn it_works_for_default_value() {
		new_test_ext().execute_with(|| {
			assert_eq!(Example::foo(), 24);
			assert_ok!(Example::accumulate_foo(Origin::signed(1), 1));
			assert_eq!(Example::foo(), 25);
		});
	}

	#[test]
	fn signed_ext_watch_dummy_works() {
		new_test_ext().execute_with(|| {
			let call = <pallet_example::Call<Test>>::set_dummy(10).into();
			let info = DispatchInfo::default();

			assert_eq!(
				WatchDummy::<Test>(PhantomData).validate(&1, &call, &info, 150)
					.unwrap()
					.priority,
				u64::max_value(),
			);
			assert_eq!(
				WatchDummy::<Test>(PhantomData).validate(&1, &call, &info, 250),
				InvalidTransaction::ExhaustsResources.into(),
			);
		})
	}

	#[test]
	fn weights_work() {
		// must have a defined weight.
		let default_call = <pallet_example::Call<Test>>::accumulate_dummy(10);
		let info = default_call.get_dispatch_info();
		// aka. `let info = <Call<Test> as GetDispatchInfo>::get_dispatch_info(&default_call);`
		assert_eq!(info.weight, 0);

		// must have a custom weight of `100 * arg = 2000`
		let custom_call = <pallet_example::Call<Test>>::set_dummy(20);
		let info = custom_call.get_dispatch_info();
		assert_eq!(info.weight, 2000);
	}
}
