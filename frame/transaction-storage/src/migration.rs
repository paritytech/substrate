use frame_support::traits::{Get, PalletInfoAccess, StorageVersion};

use crate::*;

pub struct RemoveLimitsFromStorage<T: crate::Config>(sp_std::marker::PhantomData<T>);
impl<T: crate::Config> frame_support::traits::OnRuntimeUpgrade for RemoveLimitsFromStorage<T> {
	fn on_runtime_upgrade() -> frame_support::weights::Weight {
		if StorageVersion::get::<Pallet<T>>() == 0 {
			let max_size_remove_result = frame_support::storage::migration::clear_storage_prefix(
				Pallet::<T>::name().as_bytes(),
				b"MaxTransactionSize",
				&[],
				Some(1),
				None,
			);
			if max_size_remove_result.backend != 1 {
				log::warn!(
					target: "runtime::transaction_storage",
					"Expected to remove single item 'MaxTransactionSize' from storage. {} items were removed.", max_size_remove_result.backend);
			}

			let max_block_transactions_remove_result =
				frame_support::storage::migration::clear_storage_prefix(
					Pallet::<T>::name().as_bytes(),
					b"MaxBlockTransactions",
					&[],
					Some(1),
					None,
				);

			if max_block_transactions_remove_result.backend != 1 {
				log::warn!(
					target: "runtime::transaction_storage",
					"Expected to remove single item 'MaxTransactionSize' from storage. {} items were removed.", max_size_remove_result.backend);
			}

			StorageVersion::new(1).put::<Pallet<T>>();
			T::DbWeight::get().reads_writes(2, 0)
		} else {
			log::info!(
				target: "runtime::transaction_storage",
				"No migration needed.",
			);
			0
		}
	}
}
