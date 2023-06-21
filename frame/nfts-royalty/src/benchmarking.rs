//! Benchmarking setup for nfts-royalty
#![cfg(feature = "runtime-benchmarks")]
use super::*;

#[allow(unused)]
use crate::Pallet as NftsRoyalty;
use frame_benchmarking::v2::*;
use frame_support::{
	assert_ok,
	pallet_prelude::*,
	traits::{
		tokens::nonfungibles_v2::{Create, Mutate, Buy, Destroy},
		Currency,
	},
};
use frame_system::RawOrigin;
use pallet_nfts::{CollectionConfig, CollectionSettings, ItemConfig, MintSettings};
pub use sp_runtime::Permill;

type CollectionConfigOf<T> = CollectionConfig<
	BalanceOf<T>,
	<T as SystemConfig>::BlockNumber,
	<T as Config>::NftCollectionId,
>;

// pub(super) type BalanceOf<T> =
// 	<<T as Config>::Currency as Currency<<T as SystemConfig>::AccountId>>::Balance;
pub(super) type ItemPrice<T> = BalanceOf<T>;

#[benchmarks(where
    T::NftCollectionId: From<u32>,
    T::NftItemId: From<u32>,
    T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>> 
		+ Mutate<T::AccountId, ItemConfig> + Buy<T::AccountId, ItemPrice<T>> + Destroy<T::AccountId>,
	T::Currency: Currency<T::AccountId>,
	)]
mod benchmarks {
	use super::*;

	fn default_collection_config<T: Config>() -> CollectionConfigOf<T> {
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
		//T::Currency::make_free_balance_be(&caller, 1_000_000u32.into());
		assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
		assert_ok!(T::Nfts::mint_into(
			&collection_id,
			&nft_id,
			&caller,
			&ItemConfig::default(),
			true
		));
		caller
	}

	fn create_nft_collection<T: Config>() -> (T::AccountId, T::NftCollectionId)
	where
		T::NftCollectionId: From<u32>,
		T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>,
	{
		let caller: T::AccountId = whitelisted_caller();
		let deposit = T::CollectionRoyaltyDeposit::get();
		T::Currency::make_free_balance_be(&caller, T::Currency::minimum_balance() * 1000u32.into() + deposit);
		assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
		(caller, 0.into())
	}

	#[benchmark]
	fn set_collection_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (collection_owner, collection_id) = create_nft_collection::<T>();

		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		#[extrinsic_call]
		set_collection_royalty(
			RawOrigin::Signed(caller),
			collection_id,
			Permill::from_percent(10),
			collection_owner.clone(),
			list_recipients.clone(),
		);

		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let collection_royalty_from_storage = CollectionRoyalty::<T>::get(collection_id).unwrap();

		assert_eq!(collection_royalty_from_storage.royalty_admin, collection_owner);
		assert_eq!(collection_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(collection_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(collection_royalty_from_storage.deposit, T::CollectionRoyaltyDeposit::get());
	}

	#[benchmark]
	fn set_item_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let item_owner = mint_nft::<T>(collection_id, item_id);

		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		#[extrinsic_call]
		set_item_royalty(
			RawOrigin::Signed(caller),
			collection_id,
			item_id,
			Permill::from_percent(10),
			item_owner.clone(),
			list_recipients.clone()
		);
		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

		assert_eq!(item_royalty_from_storage.royalty_admin, item_owner);
		assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(item_royalty_from_storage.deposit, T::CollectionRoyaltyDeposit::get());
	}

	#[benchmark]
	fn transfer_collection_royalty_recipient() {
		let caller: T::AccountId = whitelisted_caller();

		let (collection_owner, collection_id) = create_nft_collection::<T>();
		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		assert_ok!(NftsRoyalty::<T>::set_collection_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			Permill::from_percent(10),
			collection_owner.clone(),
			list_recipients.clone(),
		));

		let new_recipient = account::<T::AccountId>("member A", 2, 2);
		#[extrinsic_call]
		transfer_collection_royalty_recipient(
			RawOrigin::Signed(caller),
			collection_id,
			new_recipient.clone(),
		);
		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let collection_royalty_from_storage = CollectionRoyalty::<T>::get(collection_id).unwrap();

		assert_eq!(collection_royalty_from_storage.royalty_admin, new_recipient);
		assert_eq!(collection_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(collection_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(collection_royalty_from_storage.deposit, T::CollectionRoyaltyDeposit::get());
	}

	#[benchmark]
	fn transfer_item_royalty_recipient() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let item_owner = mint_nft::<T>(collection_id, item_id);

		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		assert_ok!(NftsRoyalty::<T>::set_item_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			item_id,
			Permill::from_percent(10),
			item_owner.clone(),
			list_recipients.clone()
		));

		let new_recipient = account::<T::AccountId>("member A", 2, 2);
		#[extrinsic_call]
		transfer_item_royalty_recipient(
			RawOrigin::Signed(caller),
			collection_id,
			item_id,
			new_recipient.clone(),
		);

		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

		assert_eq!(item_royalty_from_storage.royalty_admin, new_recipient);
		assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(item_royalty_from_storage.deposit, T::CollectionRoyaltyDeposit::get());
	}

	// #[benchmark]
	// fn buy() {
	// 	let caller: T::AccountId = whitelisted_caller();

	// 	let (_collection_owner, collection_id) = create_nft_collection::<T>();
	// 	let item_id = 0.into();
	// 	let item_owner = mint_nft::<T>(collection_id, item_id);

	// 	T::Nfts::set_price(&caller, collection_id,item_id, Some(100), None);

	// 	let list_recipients = vec![
	// 		RoyaltyDetails {
	// 			royalty_recipient: caller.clone(),
	// 			royalty_recipient_percentage: Permill::from_percent(50),
	// 		},
	// 	];

	// 	assert_ok!(NftsRoyalty::<T>::set_item_royalty(
	// 		RawOrigin::Signed(caller.clone()).into(),
	// 		collection_id,
	// 		item_id,
	// 		Permill::from_percent(10),
	// 		item_owner.clone(),
	// 		list_recipients.clone()
	// 	));

	// 	let new_recipient = account::<T::AccountId>("member A", 2, 2);
	// 	#[extrinsic_call]
	// 	buy(
	// 		RawOrigin::Signed(new_recipient),
	// 		collection_id,
	// 		item_id,
	// 		50.into(),
	// 	);

	// 	let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
	// 	let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

	// 	assert_eq!(item_royalty_from_storage.royalty_admin, new_recipient);
	// 	assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
	// 	assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
	// 	assert_eq!(item_royalty_from_storage.deposit, T::CollectionRoyaltyDeposit::get());
	// }

	#[benchmark]
	fn remove_collection_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (collection_owner, collection_id) = create_nft_collection::<T>();
		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		assert_ok!(NftsRoyalty::<T>::set_collection_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			Permill::from_percent(10),
			collection_owner.clone(),
			list_recipients.clone(),
		));

		let w = T::Nfts::get_destroy_witness(&collection_id).unwrap();
		assert_ok!(T::Nfts::destroy(collection_id, w, Some(caller.clone())));

		assert_eq!(T::Nfts::collections().any(|x| x == collection_id), false);


		#[extrinsic_call]
		remove_collection_royalty(
			RawOrigin::Signed(caller),
			collection_id,
		);

		assert!(!<CollectionRoyalty<T>>::contains_key(collection_id));
	}

	#[benchmark]
	fn remove_item_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let item_owner = mint_nft::<T>(collection_id, item_id);

		let list_recipients = vec![
			RoyaltyDetails {
				royalty_recipient: caller.clone(),
				royalty_recipient_percentage: Permill::from_percent(100),
			},
		];

		assert_ok!(NftsRoyalty::<T>::set_item_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			item_id,
			Permill::from_percent(10),
			item_owner.clone(),
			list_recipients.clone()
		));

		assert_ok!(T::Nfts::burn(&collection_id, &item_id, Some(&caller.clone())));

		assert_eq!(T::Nfts::items(&collection_id).any(|id| id == item_id), false);

		#[extrinsic_call]
		remove_item_royalty(
			RawOrigin::Signed(caller),
			collection_id,
			item_id,
		);

		assert!(!<ItemRoyalty<T>>::contains_key((collection_id, item_id)));

	}

	impl_benchmark_test_suite!(NftsRoyalty, crate::mock::new_test_ext(), crate::mock::Test);
}
