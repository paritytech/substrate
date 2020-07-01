use frame_support::construct_runtime;

mod system {
}

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		System: system,
	}
}

fn main() {}
