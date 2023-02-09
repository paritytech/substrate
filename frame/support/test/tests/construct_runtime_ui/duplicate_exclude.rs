use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		RuntimeExtrinsic = RuntimeExtrinsic,
		Block = Block,
		NodeBlock = Block,
	{
		System: frame_system exclude_parts { Call, Call },
	}
}

fn main() {}
