use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		#[cfg(test)]
		System: frame_system::{Pallet, Call, Storage, Config<T>, Event<T>},
	}
}

fn main() {}
