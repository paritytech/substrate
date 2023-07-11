use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = Uxt,
	{
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>},
	}
}

fn main() {}
