#![cfg_attr(not(feature = "std"), no_std)]

use frame_support::{
	traits::{
		ConstU32,
	},
};

pub use pallet::*;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	// The struct on which we build all of our Pallet logic.
	#[pallet::pallet]
	pub struct Pallet<T>(_);

	// Your Pallet's configuration trait, representing custom external types and interfaces.
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	// The MEL requirement for bounded pallets is skipped by `dev_mode`.
	#[pallet::storage]
	type MyStorage<T: Config> = StorageValue<_, Vec<u8>>;

	// The Hasher requirement skipped by `dev_mode`.
	#[pallet::storage]
	pub type MyStorageMap<T: Config> = StorageMap<_, _, u32, u64>;

	#[pallet::storage]
	type MyStorageDoubleMap<T: Config> = StorageDoubleMap<_, _, u32, _, u64, u64>;

	#[pallet::storage]
	type MyCountedStorageMap<T: Config> = CountedStorageMap<_, _, u32, u64>;

	// Your Pallet's callable functions.
	#[pallet::call]
	impl<T: Config> Pallet<T> {
		// No need to define a `weight` attribute here because of `dev_mode`.
		pub fn my_call(_origin: OriginFor<T>) -> DispatchResult {
			Ok(())
		}
	}

	// Your Pallet's internal functions.
	impl<T: Config> Pallet<T> {}
}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type RuntimeOrigin = RuntimeOrigin;
	type Index = u64;
	type BlockNumber = u32;
	type RuntimeCall = RuntimeCall;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type RuntimeEvent = RuntimeEvent;
	type BlockHashCount = ConstU32<250>;
	type BlockWeights = ();
	type BlockLength = ();
	type DbWeight = ();
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

pub type Header = sp_runtime::generic::Header<u32, sp_runtime::traits::BlakeTwo256>;
pub type Block = sp_runtime::generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = sp_runtime::generic::UncheckedExtrinsic<u32, RuntimeCall, (), ()>;

frame_support::construct_runtime!(
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		// Exclude part `Storage` in order not to check its metadata in tests.
		System: frame_system exclude_parts { Pallet, Storage },
		Example: pallet,
	}
);

impl pallet::Config for Runtime {
	
}

fn main() {
	use frame_support::{pallet_prelude::*};
	use storage::unhashed;
	use sp_io::{
		hashing::{blake2_128, twox_128},
		TestExternalities,
	};

	fn blake2_128_concat(d: &[u8]) -> Vec<u8> {
		let mut v = blake2_128(d).to_vec();
		v.extend_from_slice(d);
		v
	}

	TestExternalities::default().execute_with(|| {
		pallet::MyStorageMap::<Runtime>::insert(1, 2);
		let mut k = [twox_128(b"Example"), twox_128(b"MyStorageMap")].concat();
		k.extend(1u32.using_encoded(blake2_128_concat));
		assert_eq!(unhashed::get::<u64>(&k), Some(2u64));
	});
}
