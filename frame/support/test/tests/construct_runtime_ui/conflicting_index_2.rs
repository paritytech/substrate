use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{Pallet} = 5,
		Pallet1: pallet1::{Pallet} = 3,
		Pallet2: pallet2::{Pallet},
		Pallet3: pallet3::{Pallet},
	}
}

fn main() {}
