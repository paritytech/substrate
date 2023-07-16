use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet},
		Balance: balances::{Unexpected},
	}
}

fn main() {}
