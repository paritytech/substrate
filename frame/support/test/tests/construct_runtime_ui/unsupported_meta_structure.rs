use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		System: system::{Pallet},
		#[cfg(feature(test))]
		Balance: balances::{Config, Call},
	}
}

fn main() {}
