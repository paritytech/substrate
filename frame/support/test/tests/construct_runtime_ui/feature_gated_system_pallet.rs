use frame_support::construct_runtime;

construct_runtime! {
	pub struct Runtime
	{
		#[cfg(test)]
		System: frame_system::{Pallet, Call, Storage, Config, Event<T>},
	}
}

fn main() {}
