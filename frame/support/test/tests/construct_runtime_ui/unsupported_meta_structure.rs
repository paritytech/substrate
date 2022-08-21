use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Pallet},
		#[cfg(feature(test))]
		Balance: balances::{Config, Call},
	}
}

fn main() {}
