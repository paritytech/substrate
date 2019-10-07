use support::construct_runtime2;

construct_runtime2!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		X
	}
);
