use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		RuntimeExtrinsic = RuntimeExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{} = 255,
		Pallet256: pallet256::{},
	}
}

fn main() {}
