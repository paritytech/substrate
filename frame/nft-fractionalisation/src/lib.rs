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
		sp_runtime::traits::{
			AccountIdConversion, AtLeast32BitUnsigned, IntegerSquareRoot, StaticLookup, Zero,
		},
		traits::{
			fungibles::{
				metadata::Mutate as MutateMetadata, Create, Inspect, InspectEnumerable, Mutate,
				Transfer,
			},
			Currency,
		},
		PalletId,
	};

	pub type BalanceOf<T> =
		<<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;
	pub type AssetIdOf<T> =
		<<T as Config>::Assets as Inspect<<T as frame_system::Config>::AccountId>>::AssetId;
	pub type AssetBalanceOf<T> =
		<<T as Config>::Assets as Inspect<<T as frame_system::Config>::AccountId>>::Balance;

	pub type AccountIdLookupOf<T> = <<T as frame_system::Config>::Lookup as StaticLookup>::Source;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + pallet_uniques::Config //+ pallet_assets::Config
	{
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		type Currency: Currency<Self::AccountId>;

		type CollectionId;

		type ItemId;

		type AssetBalance: AtLeast32BitUnsigned
			+ codec::FullCodec
			+ Copy
			+ MaybeSerializeDeserialize
			+ sp_std::fmt::Debug
			+ Default
			+ From<u64>
			+ IntegerSquareRoot
			+ Zero
			+ TypeInfo
			+ MaxEncodedLen;

		type AssetId: Member
			+ Parameter
			+ Default
			+ Copy
			+ codec::HasCompact
			+ From<u32>
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen
			+ PartialOrd
			+ TypeInfo;

		type Assets: Inspect<Self::AccountId, AssetId = Self::AssetId, Balance = Self::AssetBalance>
			+ Create<Self::AccountId>
			+ InspectEnumerable<Self::AccountId>
			+ Mutate<Self::AccountId>
			+ MutateMetadata<Self::AccountId>
			+ Transfer<Self::AccountId>;

		#[pallet::constant]
		type PalletId: Get<PalletId>;
	}

	#[pallet::storage]
	#[pallet::getter(fn assets_minted)]
	// TODO: query amount minted from pallet assets instead of storing it locally.
	// Add a public getter function to pallet assets.
	pub type AssetsMinted<T: Config> =
		StorageMap<_, Twox64Concat, AssetIdOf<T>, BalanceOf<T>, OptionQuery>;

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		NFTLocked(
			<T as pallet_uniques::Config>::CollectionId,
			<T as pallet_uniques::Config>::ItemId,
		),
		AssetCreated(AssetIdOf<T>),
		AssetMinted(AssetIdOf<T>, AssetBalanceOf<T>),
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
			asset_id: AssetIdOf<T>,
			beneficiary: T::AccountId,
			min_balance: AssetBalanceOf<T>,
			amount: AssetBalanceOf<T>,
		) -> DispatchResult {
			let _who = ensure_signed(origin.clone())?;
			let admin_account_id = Self::pallet_account_id();
			let admin = T::Lookup::unlookup(admin_account_id.clone());

			match Self::do_lock_nft(origin.clone(), collection_id, item_id) {
				Err(e) => return Err(e),
				//Ok(()) => match Self::do_create_asset(origin.clone(), asset_id, admin, min_balance)
				Ok(()) => match Self::do_create_asset(asset_id, admin_account_id, min_balance) {
					Err(e) => return Err(e),
					Ok(()) => match Self::do_mint_asset(
						// Minting the asset is only possible from the pallet's origin.
						// TODO: should the minting be possible from the owner's account?
						asset_id,
						&beneficiary,
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
			asset_id: AssetIdOf<T>,
			admin: T::AccountId,
			min_balance: AssetBalanceOf<T>,
		) -> DispatchResult {
			T::Assets::create(asset_id, admin, true, min_balance)
		}

		fn do_mint_asset(
			asset_id: AssetIdOf<T>,
			beneficiary: &T::AccountId,
			amount: AssetBalanceOf<T>,
		) -> DispatchResult {
			T::Assets::mint_into(asset_id, beneficiary, amount)
		}
	}
}
