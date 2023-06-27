use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{},
		Pallet1: pallet1::{} = 0,
	}
}

fn main() {}
