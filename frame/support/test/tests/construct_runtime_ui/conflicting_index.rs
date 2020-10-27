use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{Pallet},
		Pallet1: pallet1::{Pallet} = 0,
	}
}

fn main() {}
