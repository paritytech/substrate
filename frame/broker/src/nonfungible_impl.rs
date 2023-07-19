use super::*;
use frame_support::{
	pallet_prelude::{DispatchResult, *},
	traits::nonfungible::{Inspect, Transfer},
};
use sp_std::vec::Vec;

impl<T: Config> Inspect<T::AccountId> for Pallet<T> {
	type ItemId = u128;

	fn owner(index: &Self::ItemId) -> Option<T::AccountId> {
		Regions::<T>::get(RegionId::from(*index)).map(|r| r.owner)
	}

	fn attribute(index: &Self::ItemId, key: &[u8]) -> Option<Vec<u8>> {
		let id = RegionId::from(*index);
		let item = Regions::<T>::get(id)?;
		match key {
			b"begin" => Some(id.begin.encode()),
			b"end" => Some(item.end.encode()),
			b"length" => Some(item.end.saturating_sub(id.begin).encode()),
			b"core" => Some(id.core.encode()),
			b"part" => Some(id.part.encode()),
			b"owner" => Some(item.owner.encode()),
			b"paid" => Some(item.paid.encode()),
			_ => None,
		}
	}
}

impl<T: Config> Transfer<T::AccountId> for Pallet<T> {
	fn transfer(index: &Self::ItemId, dest: &T::AccountId) -> DispatchResult {
		Self::do_transfer((*index).into(), None, dest.clone()).map_err(Into::into)
	}
}
