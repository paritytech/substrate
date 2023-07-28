use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet},
		Balance: balances::{Pallet},
		Balance: balances::{Pallet},
	}
}

fn main() {}
