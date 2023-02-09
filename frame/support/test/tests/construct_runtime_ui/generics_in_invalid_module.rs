use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		RuntimeExtrinsic = RuntimeExtrinsic
	{
		System: system::{Pallet},
		Balance: balances::<Instance1>::{Call<T>, Origin<T>},
	}
}

fn main() {}
