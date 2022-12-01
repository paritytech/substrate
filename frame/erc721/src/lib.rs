// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::marker::PhantomData;
use frame_support::{
	dispatch::{DispatchResult}, decl_module, decl_storage, decl_event, decl_error,
	ensure,
	traits::Get,
	weights::{DispatchClass, ClassifyDispatch, WeighData, Weight, PaysFee, Pays},
};
use sp_std::prelude::*;
use frame_system::{self as system, ensure_signed, ensure_root};
use sp_core::U256;
use codec::{Encode, Decode};
use sp_runtime::{
	traits::{
		SignedExtension, Bounded, SaturatedConversion, DispatchInfoOf,
	},
	transaction_validity::{
		ValidTransaction, TransactionValidityError, InvalidTransaction, TransactionValidity,
	},
	RuntimeDebug,
};

mod mock;
mod tests;

type TokenId = U256;

#[derive(PartialEq, Eq, Clone, Encode, Decode, RuntimeDebug, scale_info::TypeInfo)]
pub struct Erc721Token {
    pub id: TokenId,
    pub metadata: Vec<u8>,
}

pub trait Config: system::Config {
    type Event: From<Event<Self>> + Into<<Self as system::Config>::Event>;

    /// Some identifier for this token type, possibly the originating ethereum address.
    /// This is not explicitly used for anything, but may reflect the bridge's notion of resource ID.
    type Identifier: Get<[u8; 32]>;
}

decl_error! {
    pub enum Error for Module<T: Config> {
        /// ID not recognized
        TokenIdDoesNotExist,
        /// Already exists with an owner
        TokenAlreadyExists,
        /// Origin is not owner
        NotOwner,
    }
}

decl_storage! {
	trait Store for Module<T: Config> as TokenStorage {
        /// Maps tokenId to Erc721 object
        Tokens get(fn tokens): map hasher(opaque_blake2_256) TokenId => Option<Erc721Token>;
        /// Maps tokenId to owner
        TokenOwner get(fn owner_of): map hasher(opaque_blake2_256) TokenId => Option<T::AccountId>;
        /// Total number of tokens in existence
        TokenCount get(fn token_count): U256 = U256::zero();
    }
}

decl_event!(
	pub enum Event<T>
    where
        <T as system::Config>::AccountId,
    {
        /// New token created
        Minted(AccountId, TokenId),
        /// Token transfer between two parties
        Transferred(AccountId, AccountId, TokenId),
        /// Token removed from the system
        Burned(TokenId),
    }
);

decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::Origin {
        type Error = Error<T>;
        fn deposit_event() = default;

        /// Creates a new token with the given token ID and metadata, and gives ownership to owner
        #[weight = 195_000_000]
        pub fn mint(origin, owner: T::AccountId, id: TokenId, metadata: Vec<u8>) -> DispatchResult {
            ensure_root(origin)?;

            Self::mint_token(owner, id, metadata)?;

            Ok(())
        }

        /// Changes ownership of a token sender owns
        #[weight = 195_000_000]
        pub fn transfer(origin, to: T::AccountId, id: TokenId) -> DispatchResult {
            let sender = ensure_signed(origin)?;

            Self::transfer_from(sender, to, id)?;

            Ok(())
        }

        /// Remove token from the system
        #[weight = 195_000_000]
        pub fn burn(origin, id: TokenId) -> DispatchResult {
            ensure_root(origin)?;

            let owner = Self::owner_of(id).ok_or(Error::<T>::TokenIdDoesNotExist)?;

            Self::burn_token(owner, id)?;

            Ok(())
        }
    }
}

impl<T: Config> Module<T> {
    /// Creates a new token in the system.
    pub fn mint_token(owner: T::AccountId, id: TokenId, metadata: Vec<u8>) -> DispatchResult {
        ensure!(!Tokens::contains_key(id), Error::<T>::TokenAlreadyExists);

        let new_token = Erc721Token { id, metadata };

        <Tokens>::insert(&id, new_token);
        <TokenOwner<T>>::insert(&id, owner.clone());
        let new_total = <TokenCount>::get().saturating_add(U256::one());
        <TokenCount>::put(new_total);

        Self::deposit_event(RawEvent::Minted(owner, id));

        Ok(())
    }

    /// Modifies ownership of a token
    pub fn transfer_from(from: T::AccountId, to: T::AccountId, id: TokenId) -> DispatchResult {
        // Check from is owner and token exists
        let owner = Self::owner_of(id).ok_or(Error::<T>::TokenIdDoesNotExist)?;
        ensure!(owner == from, Error::<T>::NotOwner);
        // Update owner
        <TokenOwner<T>>::insert(&id, to.clone());

        Self::deposit_event(RawEvent::Transferred(from, to, id));

        Ok(())
    }

    /// Deletes a token from the system.
    pub fn burn_token(from: T::AccountId, id: TokenId) -> DispatchResult {
        let owner = Self::owner_of(id).ok_or(Error::<T>::TokenIdDoesNotExist)?;
        ensure!(owner == from, Error::<T>::NotOwner);

        <Tokens>::remove(&id);
        <TokenOwner<T>>::remove(&id);
        let new_total = <TokenCount>::get().saturating_sub(U256::one());
        <TokenCount>::put(new_total);

        Self::deposit_event(RawEvent::Burned(id));

        Ok(())
    }
}
