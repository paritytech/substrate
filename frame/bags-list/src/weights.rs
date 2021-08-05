use frame_support::pallet_prelude::Weight;
use frame_support::weights::constants::RocksDbWeight;

pub trait WeightInfo {
	fn rebag_middle() -> Weight;
}

pub struct SubstrateWeight<T>(std::marker::PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn rebag_middle() -> Weight {
		// FAKE numbers
		(84_501_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
}

impl WeightInfo for () {
	fn rebag_middle() -> Weight {
		// FAKE numbers
		(84_501_000 as Weight)
			.saturating_add(RocksDbWeight::get().reads(7 as Weight))
			.saturating_add(RocksDbWeight::get().writes(5 as Weight))
	}
}