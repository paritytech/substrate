//! Benchmarking setup for nfts-royalty
#![cfg(feature = "runtime-benchmarks")]
use super::*;

#[allow(unused)]
use crate::Pallet as NftsRoyalty;
use frame_benchmarking::v2::*;
use frame_system::RawOrigin;
use frame_support::{
    assert_ok,
	traits::{
		tokens::nonfungibles_v2::{Create, Mutate},
	},
};
pub use sp_runtime::{Permill};
use pallet_nfts::{CollectionConfig, CollectionSettings, MintSettings, ItemConfig};


type CollectionConfigOf<T> = CollectionConfig<
	BalanceOf<T>,
	<T as SystemConfig>::BlockNumber,
	<T as Config>::NftCollectionId,
>;


#[benchmarks(where
    T::NftCollectionId: From<u32>,
    T::NftItemId: From<u32>,
    T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
    + Mutate<T::AccountId, ItemConfig>,)]
mod benchmarks {
	use super::*;

    fn default_collection_config<T: Config>() -> CollectionConfigOf<T>
    {
        CollectionConfig {
            settings: CollectionSettings::all_enabled(),
            max_supply: None,
            mint_settings: MintSettings::default(),
        }
    }

    fn mint_nft<T: Config>(collection_id: T::NftCollectionId, nft_id: T::NftItemId) -> T::AccountId
    where
        T::NftCollectionId: From<u32>,
        T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
        + Mutate<T::AccountId, ItemConfig>,
    {
        let caller: T::AccountId = whitelisted_caller();
        //assert_ok!(T::Currency::set_balance(&caller, BalanceOf::<T>::max_value()));
        assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
        assert_ok!(T::Nfts::mint_into(&collection_id, &nft_id, &caller, &ItemConfig::default(), true));
        caller
    }

    fn create_nft_collection<T: Config>() -> (T::AccountId, T::NftCollectionId)
    where
        T::NftCollectionId: From<u32>,
        T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
        + Mutate<T::AccountId, ItemConfig>,
    {
        let caller: T::AccountId = whitelisted_caller();
        //assert_ok!(T::Currency::set_balance(&caller, BalanceOf::<T>::max_value()));
        assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
        (caller, 0.into())
    }

	#[benchmark]
	fn set_collection_royalty() {
		let caller: T::AccountId = whitelisted_caller();

        let (collection_owner, collection_id) = create_nft_collection::<T>();

		#[extrinsic_call]
		set_collection_royalty(RawOrigin::Signed(caller), collection_id, Permill::from_percent(10), collection_owner.clone());
        let royaltiy_details = RoyaltyDetails {
            royalty_recipient: collection_owner,
            royalty_percentage: Permill::from_percent(10)
        };

		assert_eq!(CollectionWithRoyalty::<T>::get(collection_id), Some(royaltiy_details));
	}

    #[benchmark]
    fn set_item_royalty() {
		let caller: T::AccountId = whitelisted_caller();

        let (_collection_owner, collection_id) = create_nft_collection::<T>();
        let item_id = 0.into();
        let item_owner = mint_nft::<T>(collection_id, item_id);

		#[extrinsic_call]
		set_item_royalty(RawOrigin::Signed(caller), collection_id,item_id, Permill::from_percent(10), item_owner.clone());
        let royaltiy_details = RoyaltyDetails {
            royalty_recipient: item_owner,
            royalty_percentage: Permill::from_percent(10)
        };

		assert_eq!(ItemWithRoyalty::<T>::get((collection_id, item_id)), Some(royaltiy_details));
	}

	impl_benchmark_test_suite!(NftsRoyalty, crate::mock::new_test_ext(), crate::mock::Test);
}