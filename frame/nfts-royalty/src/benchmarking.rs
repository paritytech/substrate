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
		tokens::nonfungibles_v2::{Buy, Create, Destroy, Mutate},
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
		T::Nfts: Create<
			T::AccountId,
			CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>,
		>,
	{
		let caller: T::AccountId = whitelisted_caller();
		let deposit = T::ItemRoyaltyDeposit::get();
		T::Currency::make_free_balance_be(
			&caller,
			T::Currency::minimum_balance() * 1000u32.into() + deposit,
		);
		assert_ok!(T::Nfts::create_collection(&caller, &caller, &default_collection_config::<T>()));
		(caller, 0.into())
	}

	fn set_price<T: Config>(collection_id: T::NftCollectionId, nft_id: T::NftItemId) -> T::AccountId
	where
		T::NftCollectionId: From<u32>,
		T::NftItemId: From<u32>,
		T::Nfts: Create<T::AccountId, CollectionConfig<BalanceOf<T>, T::BlockNumber, T::NftCollectionId>>
			+ Buy<T::AccountId, ItemPrice<T>>,
	{
		let caller: T::AccountId = whitelisted_caller();
		let price_buy = ItemPrice::<T>::from(50u32);

		assert_ok!(T::Nfts::set_price(&collection_id, &nft_id, &caller, Some(price_buy), None));

		caller
	}

	// Auxiliary function to setup list of recipients with the maximum number of recipients
	// allowed in the config.
	fn setup_list_recipients<T: Config>(len: u32) -> Vec<RoyaltyDetails<T::AccountId>> {
		let mut vector = Vec::<RoyaltyDetails<T::AccountId>>::new();
		let percentage_each = 100 / len;
		let mut pending_percentage = 100;
		for i in 0..len {
			let recipient = account::<T::AccountId>("member", i, i);
			let mut percentage = pending_percentage;
			if i < (len - 1) {
				pending_percentage = pending_percentage - percentage_each;
				percentage = percentage_each;
			}
			vector.push(RoyaltyDetails {
				royalty_recipient: recipient,
				royalty_recipient_percentage: Permill::from_percent(percentage),
			});
		}
		vector
	}

	#[benchmark]
	fn set_item_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let _item_owner = mint_nft::<T>(collection_id, item_id);

		let list_recipients = setup_list_recipients::<T>(T::MaxRecipients::get());

		#[extrinsic_call]
		set_item_royalty(
			RawOrigin::Signed(caller.clone()),
			collection_id,
			item_id,
			Permill::from_percent(10),
			list_recipients.clone(),
		);
		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

		assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(item_royalty_from_storage.depositor, Some(caller.clone()));
		assert_eq!(item_royalty_from_storage.deposit, T::ItemRoyaltyDeposit::get());
	}

	#[benchmark]
	fn transfer_item_royalty_recipient() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let _item_owner = mint_nft::<T>(collection_id, item_id);

		let mut list_recipients = setup_list_recipients::<T>(T::MaxRecipients::get() - 1);
		list_recipients.push(RoyaltyDetails {
			royalty_recipient: caller.clone(),
			royalty_recipient_percentage: Permill::from_percent(0),
		});

		assert_ok!(NftsRoyalty::<T>::set_item_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			item_id,
			Permill::from_percent(10),
			list_recipients.clone()
		));

		let new_recipient = account::<T::AccountId>("member A", 2, 2);
		#[extrinsic_call]
		transfer_item_royalty_recipient(
			RawOrigin::Signed(caller.clone()),
			collection_id,
			item_id,
			new_recipient.clone(),
		);

		let mut new_list_recipients = list_recipients.clone();

		let index = list_recipients
			.iter()
			.position(|recipient| recipient.royalty_recipient == caller)
			.unwrap();
		new_list_recipients[index].royalty_recipient = new_recipient.clone();

		let bounded_vec: BoundedVec<_, T::MaxRecipients> = new_list_recipients.try_into().unwrap();
		let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

		assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(item_royalty_from_storage.depositor, Some(caller.clone()));
		assert_eq!(item_royalty_from_storage.deposit, T::ItemRoyaltyDeposit::get());
	}

	#[benchmark]
	fn buy() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let _item_owner = mint_nft::<T>(collection_id, item_id);

		let _sender = set_price::<T>(collection_id, item_id);

		let list_recipients = setup_list_recipients::<T>(T::MaxRecipients::get());

		assert_ok!(NftsRoyalty::<T>::set_item_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			item_id,
			Permill::from_percent(10),
			list_recipients.clone()
		));

		let new_recipient = account::<T::AccountId>("member A", 2, 2);
		let price_bid = ItemPrice::<T>::from(60u32);
		T::Currency::make_free_balance_be(
			&new_recipient,
			T::Currency::minimum_balance() * 1000u32.into(),
		);
		#[extrinsic_call]
		buy(RawOrigin::Signed(new_recipient), collection_id, item_id, price_bid);

		let bounded_vec: BoundedVec<_, T::MaxRecipients> = list_recipients.try_into().unwrap();
		let item_royalty_from_storage = ItemRoyalty::<T>::get((collection_id, item_id)).unwrap();

		assert_eq!(item_royalty_from_storage.royalty_percentage, Permill::from_percent(10));
		assert_eq!(item_royalty_from_storage.recipients, bounded_vec);
		assert_eq!(item_royalty_from_storage.depositor, Some(caller.clone()));
		assert_eq!(item_royalty_from_storage.deposit, T::ItemRoyaltyDeposit::get());
	}

	#[benchmark]
	fn remove_item_royalty() {
		let caller: T::AccountId = whitelisted_caller();

		let (_collection_owner, collection_id) = create_nft_collection::<T>();
		let item_id = 0.into();
		let _item_owner = mint_nft::<T>(collection_id, item_id);

		let list_recipients = setup_list_recipients::<T>(T::MaxRecipients::get());

		assert_ok!(NftsRoyalty::<T>::set_item_royalty(
			RawOrigin::Signed(caller.clone()).into(),
			collection_id,
			item_id,
			Permill::from_percent(10),
			list_recipients.clone()
		));

		assert_ok!(T::Nfts::burn(&collection_id, &item_id, Some(&caller.clone())));

		assert_eq!(T::Nfts::items(&collection_id).any(|id| id == item_id), false);

		#[extrinsic_call]
		remove_item_royalty(RawOrigin::Signed(caller), collection_id, item_id);

		assert!(!<ItemRoyalty<T>>::contains_key((collection_id, item_id)));
	}

	impl_benchmark_test_suite!(NftsRoyalty, crate::mock::new_test_ext(), crate::mock::Test);
}
