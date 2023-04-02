use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		UncheckedExtrinsic = UncheckedExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: system::{} = 255,
		Pallet256: pallet256::{},
	}
}

fn main() {}
