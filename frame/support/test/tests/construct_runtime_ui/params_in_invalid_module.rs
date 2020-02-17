use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system::{Module},
		Balance: balances::<Instance1>::{Call(toto), Origin<I>},
	}
}

fn main() {}
