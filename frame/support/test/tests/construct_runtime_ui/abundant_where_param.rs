use frame_support::construct_runtime;

construct_runtime! {
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		Block = Block1,
		RuntimeExtrinsic = Uxt,
	{}
}

fn main() {}
