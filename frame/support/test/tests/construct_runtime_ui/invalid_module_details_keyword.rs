use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		system: System::{enum},
	}
}

fn main() {}
