use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		TypeX = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{}
}

fn main() {}
