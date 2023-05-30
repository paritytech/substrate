#[frame_support::pallet]
pub mod pallet_mbm {
	use core::marker::PhantomData;

	use crate::{self as frame_system, pallet_prelude::BlockNumberFor};
	use frame_support::pallet_prelude::*;
	use sp_runtime::traits::Block;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// A type contains the tuple of all active migrations.
		///
		/// Items can be removed from this If and only if they are finished.
		type ActiveMigrations: Mbm;

		/// Maximum weight that this pallet will use for all mbms.
		type MaxWeight: Get<Weight>;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	/// Storage map holding a list of active mbms and their encoded cursors.
	#[pallet::storage]
	pub type Actives<T: Config> = StorageMap<_, Blake2_128Concat, [u8; 16], Vec<u8>, OptionQuery>;

	/// Storage map holding a list of mbms that are finished. We only keep this to prevent against
	#[pallet::storage]
	pub type Finished<T: Config> = StorageMap<_, Blake2_128Concat, [u8; 16], ()>;

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_runtime_upgrade() -> Weight {
			// On each upgrade, inject all new migrations into the active set, if already not
			// registered.
			<T::ActiveMigrations as MbmExt>::store();
			Default::default()
		}

		// TODO: this should go to to `poll()`, same principle.
		fn on_initialize(_n: T::BlockNumber) -> Weight {
			let mut cursors = T::ActiveMigrations::get_cursor();
			let mut total_consumed_weight: Weight = Default::default();

			while Self::has_active_migrations() &&
				total_consumed_weight.all_lte(T::MaxWeight::get())
			{
				// TODO: this is not very efficient because in each `execute` we store the cursors
				// back into the overlay. But a bit hard to implement this with the tuple
				// abstraction.
				let (consumed, next_cursors) = T::ActiveMigrations::execute(cursors);
				cursors = next_cursors;
				total_consumed_weight = total_consumed_weight + consumed;
			}

			total_consumed_weight
		}
	}

	impl<T: Config> Pallet<T> {
		/// Returns true if this pallet has any mmbs that are mid-flight.
		///
		/// This can be used by eg. pause all dispatch.
		fn has_active_migrations() -> bool {
			Actives::<T>::iter().next().is_some()
		}
	}

	/// A single multi-block migration.
	pub trait Mbm {
		type Cursor: codec::Codec + Default;
		// type Identifier: codec::Codec;

		/// Execute one byte-size step of this migration.
		fn execute(previous: Self::Cursor) -> (Weight, Option<Self::Cursor>);

		/// Returns the identifier of this migration.
		fn identifier() -> [u8; 16];
	}

	pub trait MbmExt<M: Mbm, T: Config> {
		fn mark_finished();
		fn store();
		fn get_cursor() -> M::Cursor;
	}

	impl<T: Config, M: Mbm> MbmExt<M, T> for M {
		fn get_cursor() -> M::Cursor {
			Actives::<T>::get(M::identifier())
				.and_then(|bytes| M::Cursor::decode(&mut &*bytes).ok())
				.unwrap()
		}

		fn mark_finished() {
			let key = M::identifier();
			let _ = Actives::<T>::take(key);
			Finished::<T>::insert(key, ());
		}

		fn store() {
			let key = M::identifier();
			if Finished::<T>::contains_key(key) {
				return
			} else {
				let cursor = M::Cursor::default();
				let value = cursor.encode();
				Actives::<T>::insert(key, value);
			}
		}
	}

	impl<M1, M2, M3> Mbm for (M1, M2, M3)
	where
		M1: Mbm,
		M2: Mbm,
		M3: Mbm,
	{
		type Cursor = (M1, M2, M3);
		// type Identifier = (M1::Identifier, M2::Identifier, M3::Identifier);

		fn execute((prev_a, prev_b, prev_c): Self::Cursor) -> (Weight, Option<Self::Cursor>) {
			let any_executed = false;
			let mut weight_consumed: Weight = Default::default();

			let (consumed, maybe_next) = M1::execute(prev_a);
			if !consumed.is_zero() {
				weight_consumed += consumed;
				any_executed = true;
				if let Some(next) = maybe_next {
					M1::store();
				}
			} else {
				M1::mark_finished()
			}

			let (consumed, maybe_next) = M2::execute(prev_b);
			if !consumed.is_zero() {
				weight_consumed += consumed;
				any_executed = true;
				if let Some(next) = maybe_next {
					M2::store();
				}
			} else {
				M2::mark_finished()
			}

			let (consumed, maybe_next) = M3::execute(prev_c);
			if !consumed.is_zero() {
				weight_consumed += consumed;
				any_executed = true;
				if let Some(next) = maybe_next {
					M3::store();
				}
			} else {
				M3::mark_finished()
			}
		}

		fn identifier() -> [u8; 16] {
			unreachable();
			// (M1::identifier(), M2::identifier(), M3::identifier())
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::mocking;
	use frame_support::{assert_noop, assert_ok};
	use sp_io::TestExternalities;

	fn new_test_ext() -> TestExternalities {
		let mut ext = TestExternalities::new_empty();
		ext.insert(vec![1], vec![1]);
		ext.insert(vec![2], vec![2]);
		ext.insert(vec![3], vec![3]);
		ext.insert(vec![4], vec![4]);
		ext.insert(vec![5], vec![5]);
		ext
	}

	type UncheckedExtrinsic = mocking::MockUncheckedExtrinsic<Test>;
	type Block = mocking::MockBlock<Test>;

	frame_support::construct_runtime!(
		pub enum Test where
			Block = Block,
			NodeBlock = Block,
			UncheckedExtrinsic = UncheckedExtrinsic,
		{
			System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		}
	);

	#[test]
	fn it_words() {}
}
