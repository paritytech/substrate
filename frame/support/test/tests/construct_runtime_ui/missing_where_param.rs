use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime where
		Block = Block,
		NodeBlock = Block,
	{}
}

fn main() {}
