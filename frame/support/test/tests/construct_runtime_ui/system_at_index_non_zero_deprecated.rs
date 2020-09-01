use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		Balance: balances::{Config, Call, Origin<T>},
		System: system::{Module},
	}
}

fn main() {}
