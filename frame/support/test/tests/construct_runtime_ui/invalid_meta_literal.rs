use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet},
		#[cfg(feature = 1)]
		Balance: balances::{Config, Call},
	}
}

fn main() {}
