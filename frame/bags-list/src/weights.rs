use frame_support::{pallet_prelude::Weight};

pub trait WeightInfo {
	fn rebag() -> Weight;
}

pub struct SubstrateWeight<T>(sp_std::marker::PhantomData<T>);
impl<T: frame_system::Config> WeightInfo for SubstrateWeight<T> {
	fn rebag() -> Weight {
		0
	}
}

impl WeightInfo for () {
	fn rebag() -> Weight {
		0
	}
}
