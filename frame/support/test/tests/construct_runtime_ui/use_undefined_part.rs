use frame_support::construct_runtime;
use sp_runtime::{generic, traits::BlakeTwo256};
use sp_core::sr25519;

#[frame_support::pallet]
mod pallet {
	use frame_support::pallet_prelude::*;

	#[pallet::config]
	pub trait Config: frame_system::Config {}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::storage]
	type Foo<T> = StorageValue<Value=u8>;
}

pub type Signature = sr25519::Signature;
pub type BlockNumber = u64;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, RuntimeCall, Signature, ()>;

impl pallet::Config for Runtime {}

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet, Call, Storage, Config<T>, Event<T>},
		Pallet: pallet use_parts { Call },
	}
}

fn main() {}
