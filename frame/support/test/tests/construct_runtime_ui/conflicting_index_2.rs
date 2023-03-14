use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{} = 5,
		Pallet1: pallet1::{} = 3,
		Pallet2: pallet2::{},
		Pallet3: pallet3::{},
	}
}

fn main() {}
