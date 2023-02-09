use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		RuntimeExtrinsic = RuntimeExtrinsic
	{
		System: system::{Pallet},
		#[cfg(feature = 1)]
		Balance: balances::{Config, Call},
	}
}

fn main() {}
