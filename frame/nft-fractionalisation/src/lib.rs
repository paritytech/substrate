#![cfg_attr(not(feature = "std"), no_std)]

pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

pub use scale_info::Type;

pub type ItemId = <Type as pallet_uniques::Config>::ItemId;
pub type CollectionId = <Type as pallet_uniques::Config>::CollectionId;

#[frame_support::pallet]
pub mod pallet {
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	use frame_support::{
		dispatch::DispatchResult,
		sp_runtime::traits::{AccountIdConversion, StaticLookup},
		traits::Currency,
		PalletId,
	};

	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	pub type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config:
		frame_system::Config + pallet_uniques::Config + pallet_assets::Config
	{
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Currency: Currency<Self::AccountId>;

		type CollectionId;

		type ItemId;

		type AssetId;

		#[pallet::constant]
		type PalletId: Get<PalletId>;
	}

	#[pallet::storage]
	#[pallet::getter(fn assets_minted)]
	// TODO: query amount minted from pallet assets instead of storing it locally.
	// Add a public getter function to pallet assets. 
	pub type AssetsMinted<T: Config> = StorageMap<
		_,
		Twox64Concat,
		<T as pallet_assets::Config>::AssetId,
		BalanceOf<T>,
		OptionQuery,
	>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		NFTLocked(
			<T as pallet_uniques::Config>::CollectionId,
			<T as pallet_uniques::Config>::ItemId,
		),
		AssetCreated(<T as pallet_assets::Config>::AssetId),
		AssetMinted(<T as pallet_assets::Config>::AssetId, <T as pallet_assets::Config>::Balance),
	}

	#[pallet::error]
	pub enum Error<T> {
		AssetAlreadyRegistered,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(10_000 + T::DbWeight::get().writes(2).ref_time())]
		pub fn lock_nft_create_asset(
			origin: OriginFor<T>,
			collection_id: <T as pallet_uniques::Config>::CollectionId,
			item_id: <T as pallet_uniques::Config>::ItemId,
			asset_id: <T as pallet_assets::Config>::AssetId,
			beneficiary: AccountIdLookupOf<T>,
			min_balance: <T as pallet_assets::Config>::Balance,
			amount: <T as pallet_assets::Config>::Balance,
		) -> DispatchResult {
			let _who = ensure_signed(origin.clone())?;
			let admin_account_id = Self::pallet_account_id();
			let admin = T::Lookup::unlookup(admin_account_id.clone());

			match Self::do_lock_nft(origin.clone(), collection_id, item_id) {
				Err(e) => return Err(e),
				Ok(()) => match Self::do_create_asset(origin.clone(), asset_id, admin, min_balance)
				{
					Err(e) => return Err(e),
					Ok(()) => match Self::do_mint_asset(
						// Minting the asset is only possible from the pallet's origin.
						// TODO: should the minting be possible from the owner's account?
						frame_system::RawOrigin::Signed(admin_account_id).into(),
						asset_id,
						beneficiary,
						amount,
					) {
						Err(e) => return Err(e),
						Ok(()) => {
							Self::deposit_event(Event::NFTLocked(collection_id, item_id));
							Self::deposit_event(Event::AssetCreated(asset_id));
							Self::deposit_event(Event::AssetMinted(asset_id, amount));
						},
					},
				},
			};

			Ok(())
		}


		// TODO: return and burn 100% of the asset, unlock the NFT.
		// pub fn burn_asset_unlock_nft() -> DispatchResult {}
	}

	impl<T: Config> Pallet<T> {
		fn pallet_account_id() -> T::AccountId {
			T::PalletId::get().into_account_truncating()
		}

		fn do_lock_nft(
			who: OriginFor<T>,
			collection_id: <T as pallet_uniques::Config>::CollectionId,
			item_id: <T as pallet_uniques::Config>::ItemId,
		) -> DispatchResult {
			let pallet_id = T::Lookup::unlookup(Self::pallet_account_id());
			<pallet_uniques::Pallet<T>>::transfer(who, collection_id, item_id, pallet_id)
		}

		fn do_create_asset(
			who: OriginFor<T>,
			asset_id: <T as pallet_assets::Config>::AssetId,
			admin: AccountIdLookupOf<T>,
			min_balance: <T as pallet_assets::Config>::Balance,
		) -> DispatchResult {
			<pallet_assets::Pallet<T>>::create(who, asset_id, admin, min_balance)
		}

		fn do_mint_asset(
			who: OriginFor<T>,
			asset_id: <T as pallet_assets::Config>::AssetId,
			beneficiary: AccountIdLookupOf<T>,
			amount: <T as pallet_assets::Config>::Balance,
		) -> DispatchResult {
			<pallet_assets::Pallet<T>>::mint(who, asset_id, beneficiary, amount)
		}
	}
}
