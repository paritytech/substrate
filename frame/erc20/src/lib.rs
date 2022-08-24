// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use pallet_chainbridge as bridge;
use pallet_erc721 as erc721;

use sp_std::marker::PhantomData;
use frame_support::{
	dispatch::{DispatchResult}, decl_module, decl_storage, decl_event, decl_error,
	traits::{Currency, EnsureOrigin, ExistenceRequirement::AllowDeath, Get},
	ensure,
	weights::{DispatchClass, ClassifyDispatch, WeighData, Weight, PaysFee, Pays},
};
use sp_std::prelude::*;
use frame_system::{self as system, ensure_signed, ensure_root};
use sp_arithmetic::traits::SaturatedConversion;
use sp_core::U256;
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{
		SignedExtension, Bounded, DispatchInfoOf, UniqueSaturatedInto,
	},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
	},
};

type ResourceId = bridge::ResourceId;

type BalanceOf<T> =
    <<T as Config>::Currency as Currency<<T as frame_system::Config>::AccountId>>::Balance;

pub trait Config: system::Config + bridge::Config + erc721::Config {
    type Event: From<Event<Self>> + Into<<Self as frame_system::Config>::Event>;
    /// Specifies the origin check provided by the bridge for calls that can only be called by the bridge pallet
    type BridgeOrigin: EnsureOrigin<Self::Origin, Success = Self::AccountId>;

    /// The currency mechanism.
    type Currency: Currency<Self::AccountId>;

    /// Ids can be defined by the runtime and passed in, perhaps from blake2b_128 hashes.
    type HashId: Get<ResourceId>;
    type NativeTokenId: Get<ResourceId>;
    type Erc721Id: Get<ResourceId>;
}

decl_error! {
    pub enum Error for Module<T: Config>{
        InvalidTransfer,
    }
}

decl_event!(
    pub enum Event<T> where
        <T as frame_system::Config>::Hash,
    {
        Remark(Hash),
    }
);

decl_module! {
    pub struct Module<T: Config> for enum Call where origin: T::Origin {
        const HashId: ResourceId = T::HashId::get();
        const NativeTokenId: ResourceId = T::NativeTokenId::get();
        const Erc721Id: ResourceId = T::Erc721Id::get();

        fn deposit_event() = default;

        //
        // Initiation calls. These start a bridge transfer.
        //

        /// Transfers an arbitrary hash to a (whitelisted) destination chain.
        #[weight = 195_000_000]
        pub fn transfer_hash(origin, hash: T::Hash, dest_id: bridge::ChainId) -> DispatchResult {
            ensure_signed(origin)?;

            let resource_id = T::HashId::get();
            let metadata: Vec<u8> = hash.as_ref().to_vec();
            <bridge::Module<T>>::transfer_generic(dest_id, resource_id, metadata)
        }

        /// Transfers some amount of the native token to some recipient on a (whitelisted) destination chain.
        #[weight = 195_000_000]
        pub fn transfer_native(origin, amount: BalanceOf<T>, recipient: Vec<u8>, dest_id: bridge::ChainId) -> DispatchResult {
            let source = ensure_signed(origin)?;
            ensure!(<bridge::Module<T>>::chain_whitelisted(dest_id), Error::<T>::InvalidTransfer);
            let bridge_id = <bridge::Module<T>>::account_id();
            T::Currency::transfer(&source, &bridge_id, amount.into(), AllowDeath)?;

            let resource_id = T::NativeTokenId::get();
			let number_amount: u128 = amount.saturated_into();

            <bridge::Module<T>>::transfer_fungible(dest_id, resource_id, recipient, U256::from(number_amount))
        }


        /// Transfer a non-fungible token (erc721) to a (whitelisted) destination chain.
        #[weight = 195_000_000]
        pub fn transfer_erc721(origin, recipient: Vec<u8>, token_id: U256, dest_id: bridge::ChainId) -> DispatchResult {
            let source = ensure_signed(origin)?;
            ensure!(<bridge::Module<T>>::chain_whitelisted(dest_id), Error::<T>::InvalidTransfer);
            match <erc721::Module<T>>::tokens(&token_id) {
                Some(token) => {
                    <erc721::Module<T>>::burn_token(source, token_id)?;
                    let resource_id = T::Erc721Id::get();
                    let tid: &mut [u8] = &mut[0; 32];
                    token_id.to_big_endian(tid);
                    <bridge::Module<T>>::transfer_nonfungible(dest_id, resource_id, tid.to_vec(), recipient, token.metadata)
                }
                None => Err(Error::<T>::InvalidTransfer)?
            }
        }

        //
        // Executable calls. These can be triggered by a bridge transfer initiated on another chain
        //

        /// Executes a simple currency transfer using the bridge account as the source
        #[weight = 195_000_000]
        pub fn transfer(origin, to: T::AccountId, amount: BalanceOf<T>) -> DispatchResult {
            let source = T::BridgeOrigin::ensure_origin(origin)?;
            <T as Config>::Currency::transfer(&source, &to, amount.into(), AllowDeath)?;
            Ok(())
        }

        /// This can be called by the bridge to demonstrate an arbitrary call from a proposal.
        #[weight = 195_000_000]
        pub fn remark(origin, hash: T::Hash) -> DispatchResult {
            T::BridgeOrigin::ensure_origin(origin)?;
            Self::deposit_event(RawEvent::Remark(hash));
            Ok(())
        }

        /// Allows the bridge to issue new erc721 tokens
        #[weight = 195_000_000]
        pub fn mint_erc721(origin, recipient: T::AccountId, id: U256, metadata: Vec<u8>) -> DispatchResult {
            T::BridgeOrigin::ensure_origin(origin)?;
            <erc721::Module<T>>::mint_token(recipient, id, metadata)?;
            Ok(())
        }
    }
}
