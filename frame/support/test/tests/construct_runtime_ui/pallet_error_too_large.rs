use frame_support::construct_runtime;
use sp_runtime::{generic, traits::BlakeTwo256};
use sp_core::sr25519;

#[frame_support::pallet]
mod pallet {
	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(core::marker::PhantomData<T>);

	#[pallet::error]
	pub enum Error<T> {
		MyError(crate::Nested1),
	}
}

#[derive(scale_info::TypeInfo, frame_support::PalletError, codec::Encode, codec::Decode)]
pub enum Nested1 {
	Nested2(Nested2)
}

#[derive(scale_info::TypeInfo, frame_support::PalletError, codec::Encode, codec::Decode)]
pub enum Nested2 {
	Nested3(Nested3)
}

#[derive(scale_info::TypeInfo, frame_support::PalletError, codec::Encode, codec::Decode)]
pub enum Nested3 {
	Nested4(Nested4)
}

#[derive(scale_info::TypeInfo, frame_support::PalletError, codec::Encode, codec::Decode)]
pub enum Nested4 {
	Num(u8)
}

pub type Signature = sr25519::Signature;
pub type BlockNumber = u32;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, Call, Signature, ()>;

impl pallet::Config for Runtime {}

impl frame_system::Config for Runtime {
	type BaseCallFilter = frame_support::traits::Everything;
	type Origin = Origin;
	type Index = u64;
	type BlockNumber = u32;
	type Call = Call;
	type Hash = sp_runtime::testing::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type AccountId = u64;
	type Lookup = sp_runtime::traits::IdentityLookup<Self::AccountId>;
	type Header = Header;
	type Event = Event;
	type BlockHashCount = frame_support::traits::ConstU32<250>;
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
	type MaxConsumers = frame_support::traits::ConstU32<16>;
}

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>},
		Pallet: pallet::{Pallet},
	}
}

fn main() {}
