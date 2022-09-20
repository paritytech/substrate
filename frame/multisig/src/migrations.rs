use super::*;
use frame_support::{
	dispatch::GetStorageVersion,
	traits::{OnRuntimeUpgrade, WrapperKeepOpaque},
	Identity,
};

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

pub mod v1 {
	use super::*;

	type OpaqueCall<T> = WrapperKeepOpaque<<T as Config>::RuntimeCall>;

	#[frame_support::storage_alias]
	type Calls<T: Config> = StorageMap<
		Pallet<T>,
		Identity,
		[u8; 32],
		(OpaqueCall<T>, <T as frame_system::Config>::AccountId, BalanceOf<T>),
	>;

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain < 1, "this migration can be deleted");

			log!(info, "Number of calls to refund and delete: {}", Calls::<T>::iter().count());

			Ok(())
		}

		fn on_runtime_upgrade() -> Weight {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			if onchain > 0 {
				log!(info, "MigrateToV1 should be removed");
				return T::DbWeight::get().reads(1)
			}

			// TODO: Assuming this is one read
			let calls_read = Calls::<T>::iter().count() as u64;

			// TODO: Assuming this is one write and a read per record
			Calls::<T>::drain().for_each(|(_call_hash, (_data, caller, deposit))| {
				//TODO: What's the weight of one unreserve?
				T::Currency::unreserve(&caller, deposit);
			});

			current.put::<Pallet<T>>();

			T::DbWeight::get().reads_writes(calls_read + 1, 2)
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain > 0, "this migration needs to be run");
			ensure!(
				Calls::<T>::iter().count() == 0,
				"there are some dangling calls that need to be destroyed and refunded"
			);
			Ok(())
		}
	}
}
