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
pub type BlockNumber = u64;
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<u32, Call, Signature, ()>;

impl pallet::Config for Runtime {}

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet, Call, Storage, Config, Event<T>},
		Pallet: pallet::{Pallet},
	}
}

fn main() {}
