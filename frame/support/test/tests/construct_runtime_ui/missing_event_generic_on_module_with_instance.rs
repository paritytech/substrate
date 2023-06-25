use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet},
		Balance: balances::<Instance1>::{Event},
	}
}

fn main() {}
