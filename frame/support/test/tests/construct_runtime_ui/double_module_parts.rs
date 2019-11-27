use support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system,
		Balance: balances::{Config, Call, Config<T>, Origin<T>},
	}
}

fn main() {}
