use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet},
		Balance: balances::{Pallet},
		Balance: balances::{Pallet},
	}
}

fn main() {}
