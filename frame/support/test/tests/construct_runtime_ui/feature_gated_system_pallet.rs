use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		#[cfg(test)]
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>},
	}
}

fn main() {}
