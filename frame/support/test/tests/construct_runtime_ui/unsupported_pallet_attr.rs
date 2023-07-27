use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet},
		#[attr]
		Balance: balances::{Config, Call},
	}
}

fn main() {}
