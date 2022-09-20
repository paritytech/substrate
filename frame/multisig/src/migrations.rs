use super::*;
use frame_support::{
	traits::{OnRuntimeUpgrade, WrapperKeepOpaque},
	Blake2_256,
};

#[cfg(feature = "try-runtime")]
use frame_support::ensure;

pub mod v1 {
	use super::*;

	type OpaqueCall<T> = WrapperKeepOpaque<<T as Config>::RuntimeCall>;

	#[frame_support::storage_alias]
	type Calls<T: Config> = StorageMap<
		crate::Pallet<T>,
		Blake2_256,
		[u8; 32],
		(OpaqueCall<T>, T::AccountId, BalanceOf<T>),
	>;

	pub struct MigrateToV1<T>(sp_std::marker::PhantomData<T>);
	impl<T: Config> OnRuntimeUpgrade for MigrateToV1<T> {
		#[cfg(feature = "try-runtime")]
		fn pre_upgrade() -> Result<(), &'static str> {
			let current = Pallet::<T>::current_storage_version();
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain < 1, "this migration can be deleted");

			log!(info, "Number of calls to refund and delete: {}", Calls<T>::count());

			Ok(())
		}

		fn on_runtime_upgrade() -> Weight {
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain > 0, "this migration can be deleted");

			let calls = Calls::<T>::drain().for_each(|call_hash, (_data, caller, deposit)| {
				T::Currency::unreserve(&caller, deposit)?;
			});
		}

		#[cfg(feature = "try-runtime")]
		fn post_upgrade() -> Result<(), &'static str> {
			let onchain = Pallet::<T>::on_chain_storage_version();

			ensure!(onchain > 0, "this migration needs to be run");
			ensure!(Calls<T>::count() == 0,
				"there are some dangling calls that need to be destroyed and refunded");
		}
	}
}
