use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system expanded::{}::{Pallet},
		Balance: balances::<Instance1> expanded::{}::{Event},
	}
}

fn main() {}
