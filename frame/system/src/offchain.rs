// Copyright 2019-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Module helpers for off-chain calls.
//!
//! ## Overview
//!
//! This module provides transaction related helpers to:
//! - Submit a raw unsigned transaction
//! - Submit an unsigned transaction with a signed payload
//! - Submit a signed transction.
//!
//! ## Usage
//!
//! ### Submit a raw unsigned transaction
//!
//! To submit a raw unsigned transaction, [`SubmitTransaction`](./struct.SubmitTransaction.html)
//! can be used.
//!
//! ```rust
//! SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call)
//! ```
//!
//! ### Signing transactions
//!
//! To be able to use signing, the following trait should be implemented:
//!
//! - [`AppCrypto`](./trait.AppCrypto.html): where an application-specific key
//!   is defined and can be used by this module's helpers for signing.
//! - [`CreateSignedTransaction`](./trait.CreateSignedTransaction.html): where
//!   the manner in which the transaction is constructed is defined.
//!
//! #### Submit an unsigned transaction with a signed payload
//!
//! Initially, a payload instance that implements the `SignedPayload` trait should be defined.
//! If we take the [`PricePayload`](../../example-offchain-worker/struct.PricePayload.html)
//! defined in the example-offchain-worker pallet, we see the following:
//!
//! ```rust
//! #[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
//! pub struct PricePayload<Public, BlockNumber> {
//! 	block_number: BlockNumber,
//! 	price: u32,
//! 	public: Public,
//! }
//!
//! impl<T: SigningTypes> SignedPayload<T> for PricePayload<T::Public, T::BlockNumber> {
//! 	fn public(&self) -> T::Public {
//! 		self.public.clone()
//! 	}
//! }
//! ```
//!
//! An object from the defined payload can then be signed and submitted onchain.
//!
//! ```
//! Signer::<T, T::AuthorityId>::all_accounts().send_unsigned_transaction(
//! 	|account| PricePayload {
//! 		price,
//! 		block_number,
//! 		public: account.public.clone()
//! 	},
//! 	|payload, signature| {
//! 		Call::submit_price_unsigned_with_signed_payload(payload, signature)
//! 	}
//! )
//! ```
//!
//! #### Submit a signed transaction
//!
//! ```
//! Signer::<T, T::AuthorityId>::all_accounts().send_signed_transaction(
//! 	|account| Call::submit_price(price)
//! );

use codec::Encode;
use sp_std::convert::{TryInto, TryFrom};
use sp_std::prelude::Vec;
use sp_runtime::app_crypto::RuntimeAppPublic;
use sp_runtime::traits::{Extrinsic as ExtrinsicT, IdentifyAccount, One};
use frame_support::{debug, storage::StorageMap};

/// Marker struct used to flag using all supported keys to sign a payload.
pub struct ForAll {}
/// Marker struct used to flag using any of the supported keys to sign a payload.
pub struct ForAny {}

/// Provides the ability to directly submit signed and unsigned
/// transaction onchain.
///
/// For submitting unsigned transactions, `submit_unsigned_transaction`
/// utility function can be used. However, this struct is used by `Signer`
/// to submit a signed transactions providing the signature along with the call.
pub struct SubmitTransaction<T: SendTransactionTypes<OverarchingCall>, OverarchingCall> {
	_phantom: sp_std::marker::PhantomData<(T, OverarchingCall)>
}

impl<T, LocalCall> SubmitTransaction<T, LocalCall>
where
	T: SendTransactionTypes<LocalCall>,
{
	/// Submit transaction onchain by providing the call and an optional signature
	pub fn submit_transaction(
		call: <T as SendTransactionTypes<LocalCall>>::OverarchingCall,
		signature: Option<<T::Extrinsic as ExtrinsicT>::SignaturePayload>,
	) -> Result<(), ()> {
		let xt = T::Extrinsic::new(call.into(), signature).ok_or(())?;
		sp_io::offchain::submit_transaction(xt.encode())
	}

	/// A convenience method to submit an unsigned transaction onchain.
	pub fn submit_unsigned_transaction(
		call: <T as SendTransactionTypes<LocalCall>>::OverarchingCall,
	) -> Result<(), ()> {
		SubmitTransaction::<T, LocalCall>::submit_transaction(call, None)
	}
}

/// Provides an implementation for signing transaction payloads.
///
/// Keys used for signing are defined when instantiating the signer object.
/// Signing can be done using:
///
/// - All supported keys in the keystore
/// - Any of the supported keys in the keystore
/// - An intersection of in-keystore keys and the list of provided keys
///
/// The signer is then able to:
/// - Submit a unsigned transaction with a signed payload
/// - Submit a signed transaction
pub struct Signer<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>, X = ForAny> {
	accounts: Option<Vec<T::Public>>,
	_phantom: sp_std::marker::PhantomData<(X, C)>,
}

impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>, X> Default for Signer<T, C, X> {
	fn default() -> Self {
		Self {
			accounts: Default::default(),
			_phantom: Default::default(),
		}
	}
}

impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>, X> Signer<T, C, X> {
	/// Use all available keys for signing.
	pub fn all_accounts() -> Signer<T, C, ForAll> {
		Default::default()
	}

	/// Use any of the available keys for signing.
	pub fn any_account() -> Signer<T, C, ForAny> {
		Default::default()
	}

	/// Use provided `accounts` for signing.
	///
	/// Note that not all keys will be necessarily used. The provided
	/// vector of accounts will be intersected with the supported keys
	/// in the keystore and the resulting list will be used for signing.
	pub fn with_filter(mut self, accounts: Vec<T::Public>) -> Self {
		self.accounts = Some(accounts);
		self
	}

	/// Check if there are any keys that could be used for signing.
	pub fn can_sign(&self) -> bool {
		self.accounts_from_keys().len() > 0
	}

	/// Return a vector of the intersection between
	/// all available accounts and the provided accounts
	/// in `with_filter`. If no accounts are provided,
	/// use all accounts by default.
	fn accounts_from_keys(&self) -> Vec<Account<T>> {
		let keystore_accounts = self.keystore_accounts();

		if self.accounts.as_ref().unwrap_or(&Vec::new()).len() == 0 {
			return keystore_accounts;
		}

		let mut intersecting_accounts = vec![];
		if let Some(ref keys) = self.accounts {
			for (index, key) in keys.iter().enumerate() {
				let account_id = key.clone().into_account();
				let account = Account::new(index, account_id, key.clone());
				intersecting_accounts.push(account);
			}
		}
		intersecting_accounts
	}

	fn keystore_accounts(&self) -> Vec<Account<T>> {
		let mut accounts = vec![];
		let runtime_keys = C::RuntimeAppPublic::all()
			.into_iter()
			.enumerate();

		for (index, key) in runtime_keys {
			let generic_public = C::GenericPublic::from(key);
			let public = generic_public.into();
			let account_id = public.clone().into_account();
			let account = Account::new(index, account_id, public.clone());
			accounts.push(account);
		}

		accounts
	}
}


impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>> Signer<T, C, ForAll> {
	fn for_all<F, R>(&self, f: F) -> Vec<(Account<T>, R)> where
		F: Fn(&Account<T>) -> Option<R>,
	{
		let accounts = self.accounts_from_keys();
		accounts
			.into_iter()
			.filter_map(|account| {
				f(&account).map(|res| (account, res))
			})
			.collect()
	}
}

impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>> Signer<T, C, ForAny> {
	fn for_any<F, R>(&self, f: F) -> Option<(Account<T>, R)> where
		F: Fn(&Account<T>) -> Option<R>,
	{
		let accounts = self.accounts_from_keys();
		for account in accounts.into_iter() {
			let res = f(&account);
			if let Some(res) = res {
				return Some((account, res));
			}
		}
		None
	}
}

impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>> SignMessage<T> for Signer<T, C, ForAll> {
	type Result = Vec<(Account<T>, T::Signature)>;

	fn sign_message(&self, message: &[u8]) -> Self::Result {
		self.for_all(|account| C::sign(message, account.public.clone()))
	}

	fn sign<TPayload, F>(&self, f: F) -> Self::Result where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T>,
	{
		self.for_all(|account| f(account).sign::<C>())
	}
}

impl<T: SigningTypes, C: AppCrypto<T::Public, T::Signature>> SignMessage<T> for Signer<T, C, ForAny> {
	type Result = Option<(Account<T>, T::Signature)>;

	fn sign_message(&self, message: &[u8]) -> Self::Result {
		self.for_any(|account| C::sign(message, account.public.clone()))
	}

	fn sign<TPayload, F>(&self, f: F) -> Self::Result where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T>,
	{
		self.for_any(|account| f(account).sign::<C>())
	}
}

impl<
	T: CreateSignedTransaction<LocalCall> + SigningTypes,
	C: AppCrypto<T::Public, T::Signature>,
	LocalCall,
> SendSignedTransaction<T, C, LocalCall> for Signer<T, C, ForAny> {
	type Result = Option<(Account<T>, Result<(), ()>)>;

	fn send_signed_transaction(
		&self,
		f: impl Fn(&Account<T>) -> LocalCall,
	) -> Self::Result {
			self.for_any(|account| {
			let call = f(account);
			self.submit_signed_transaction(account, call)
		})
	}
}

impl<
	T: SigningTypes + CreateSignedTransaction<LocalCall>,
	C: AppCrypto<T::Public, T::Signature>,
	LocalCall,
> SendSignedTransaction<T, C, LocalCall> for Signer<T, C, ForAll> {
	type Result = Vec<(Account<T>, Result<(), ()>)>;

	fn send_signed_transaction(
		&self,
		f: impl Fn(&Account<T>) -> LocalCall,
	) -> Self::Result {
		self.for_all(|account| {
			let call = f(account);
			self.submit_signed_transaction(account, call)
		})
	}
}

impl<
	T: SigningTypes + SendTransactionTypes<LocalCall>,
	C: AppCrypto<T::Public, T::Signature>,
	LocalCall,
> SendUnsignedTransaction<T, LocalCall> for Signer<T, C, ForAny> {
	type Result = Option<(Account<T>, Result<(), ()>)>;

	fn send_unsigned_transaction<TPayload, F>(
		&self,
		f: F,
		f2: impl Fn(TPayload, T::Signature) -> LocalCall,
	) -> Self::Result
	where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T>, 
	{
		self.for_any(|account| {
			let payload = f(account);
			let signature= payload.sign::<C>()?;
			let call = f2(payload, signature);
			self.submit_unsigned_transaction(call)
		})
	}
}

impl<
	T: SigningTypes + SendTransactionTypes<LocalCall>,
	C: AppCrypto<T::Public, T::Signature>,
	LocalCall,
> SendUnsignedTransaction<T, LocalCall> for Signer<T, C, ForAll> {
	type Result = Vec<(Account<T>, Result<(), ()>)>;

	fn send_unsigned_transaction<TPayload, F>(
		&self,
		f: F,
		f2: impl Fn(TPayload, T::Signature) -> LocalCall,
	) -> Self::Result
	where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T> {
		self.for_all(|account| {
			let payload = f(account);
			let signature = payload.sign::<C>()?;
			let call = f2(payload, signature);
			self.submit_unsigned_transaction(call)
		})
	}
}

/// Account information used for signing payloads
pub struct Account<T: SigningTypes> {
	pub index: usize,
	pub id: T::AccountId,
	pub public: T::Public,
}

impl<T: SigningTypes> Account<T> {
	/// Create a new Account instance
	pub fn new(index: usize, id: T::AccountId, public: T::Public) -> Self {
		Self { index, id, public }
	}
}

impl<T: SigningTypes> Clone for Account<T> where
	T::AccountId: Clone,
	T::Public: Clone,
{
	fn clone(&self) -> Self {
		Self {
			index: self.index,
			id: self.id.clone(),
			public: self.public.clone(),
		}
	}
}

/// App specific crypto trait that provides sign/verify
/// abilities to offchain workers. Implementations of this
/// trait should specify the app-specific public/signature
/// types.
pub trait AppCrypto<Public, Signature> {
	type RuntimeAppPublic: RuntimeAppPublic;
	// TODO [ToDr] The conversions are messy, clean them up.
	//
	// The idea would be to have some implementation for `RuntimeAppPublic`
	// to convert to and from generic types.
	// Maybe even a method like:
	// impl RuntimeAppPublic {
	//  fn into_public<T: From<Self::Generic>>(&self) -> T;
	// }
	// so an ability to convert the runtime app public into
	// some type that is reachable from the inner (wrapped) generic
	// crypto type.
	// So example:
	// ImOnline(sr25519) = RuntimeAppPublic
	// sr25519 = Generic
	// MutliSigner = From<sr25519>
	type GenericPublic:
		From<Self::RuntimeAppPublic>
		+ Into<Self::RuntimeAppPublic>
		+ TryFrom<Public>
		+ Into<Public>;
	type GenericSignature:
		From<<Self::RuntimeAppPublic as RuntimeAppPublic>::Signature>
		+ Into<<Self::RuntimeAppPublic as RuntimeAppPublic>::Signature>
		+ TryFrom<Signature>
		+ Into<Signature>;

	/// Sign payload with the private key to maps to the provided public key.
	fn sign(payload: &[u8], public: Public) -> Option<Signature> {
		let p: Self::GenericPublic = public.try_into().ok()?;
		let x = Into::<Self::RuntimeAppPublic>::into(p);
		x.sign(&payload)
			.map(|x| {
				let sig: Self::GenericSignature = x.into();
				sig
			})
			.map(Into::into)
	}

	/// Verify signature against the provided public key.
	fn verify(payload: &[u8], public: Public, signature: Signature) -> bool {
		let p: Self::GenericPublic = match public.try_into() {
			Ok(a) => a,
			_ => return false
		};
		let x = Into::<Self::RuntimeAppPublic>::into(p);
		let signature: Self::GenericSignature = match signature.try_into() {
			Ok(a) => a,
			_ => return false
		};
		let signature = Into::<<
			Self::RuntimeAppPublic as RuntimeAppPublic
		>::Signature>::into(signature);

		x.verify(&payload, &signature)
	}

}

/// A wrapper around the types which are used for signing transactions.
/// This trait should be implemented on the runtime.
pub trait SigningTypes: crate::Trait {
	// TODO [ToDr] Could this be just `T::Signature as traits::Verify>::Signer`?
	// Seems that this may cause issues with bounds resolution.
	type Public: Clone
		+ PartialEq
		+ IdentifyAccount<AccountId = Self::AccountId>
		+ core::fmt::Debug
		+ codec::Codec;
	type Signature: Clone
		+ PartialEq
		+ core::fmt::Debug
		+ codec::Codec;
}

/// A wrapper around the transaction and call types.
pub trait SendTransactionTypes<LocalCall> {
	/// The extrinsic type that this runtime submits onchain.
	type Extrinsic: ExtrinsicT<Call=Self::OverarchingCall> + codec::Encode;
	/// The runtime's call type.
	type OverarchingCall: From<LocalCall>;
}

/// Create signed transaction.
///
/// Should be implemented by the runtime to sign transaction data
pub trait CreateSignedTransaction<LocalCall>: SendTransactionTypes<LocalCall> + SigningTypes {
	/// Attempt to create signed extrinsic data that encodes call from given account.
	///
	/// Runtime implementation is free to construct the payload to sign and the signature
	/// in any way it wants.
	/// Returns `None` if signed extrinsic could not be created (either because signing failed
	/// or because of any other runtime-specific reason).
	fn create_transaction<C: AppCrypto<Self::Public, Self::Signature>>(
		call: Self::OverarchingCall,
		public: Self::Public,
		account: Self::AccountId,
		nonce: Self::Index,
	) -> Option<(Self::OverarchingCall, <Self::Extrinsic as ExtrinsicT>::SignaturePayload)>;
}

/// Sign message payload
pub trait SignMessage<T: SigningTypes> {
	type Result;

	/// Sign message
	///
	/// Implementation of this method should return
	/// a result containing the signature
	fn sign_message(&self, message: &[u8]) -> Self::Result;

	/// Sign payload
	///
	/// This method expects `f` to return a `SignedPayload`
	/// object which is then used for signing.
	///
	/// Returns a result that contains the signature of the payload.
	fn sign<TPayload, F>(&self, f: F) -> Self::Result where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T>,
		;
}

/// Submit a signed transaction onchain
pub trait SendSignedTransaction<
	T: SigningTypes + CreateSignedTransaction<LocalCall>,
	C: AppCrypto<T::Public, T::Signature>,
	LocalCall
> {
	type Result;

	/// Send a signed onchain transaction
	///
	/// Calls `f` and expects a Call object to be returned.
	/// The call object is then signed and submitted onchain.
	///
	/// Returns a result of the onchain submission.
	fn send_signed_transaction(
		&self,
		f: impl Fn(&Account<T>) -> LocalCall,
	) -> Self::Result;

	/// Performs signing and submitting the transaction onchain.
	///
	/// This method can be used by implementations of `send_signed_transaction`
	/// to actually sign and submit the signed transaction.
	///
	/// Returns a result of the onchain submittion.
	fn submit_signed_transaction(
		&self,
		account: &Account<T>,
		call: LocalCall
	) -> Option<Result<(), ()>> {
		let mut account_data = crate::Account::<T>::get(&account.id);
		debug::native::debug!(
			target: "offchain",
			"Creating signed transaction from account: {:?} (nonce: {:?})",
			account.id,
			account_data.nonce,
		);
		let (call, signature) = T::create_transaction::<C>(
			call.into(),
			account.public.clone(),
			account.id.clone(),
			account_data.nonce
		)?;
		let res = SubmitTransaction::<T, LocalCall>
			::submit_transaction(call, Some(signature));

		if res.is_ok() {
			// increment the nonce. This is fine, since the code should always
			// be running in off-chain context, so we NEVER persists data.
			account_data.nonce += One::one();
			crate::Account::<T>::insert(&account.id, account_data);
		}

		Some(res)
	}
}

/// Submit an unsigned transaction onchain with a signed payload
pub trait SendUnsignedTransaction<
	T: SigningTypes + SendTransactionTypes<LocalCall>,
	LocalCall,
> {
	type Result;

	/// Send an unsigned transaction with a signed payload.
	///
	/// This method takes `f` and `f2` where:
	/// - `f` is called and expected to return a `SignedPayload` object.
	/// - `f2` is called with the SignedPayload returned by `f` and expected to return a Call object.
	fn send_unsigned_transaction<TPayload, F>(
		&self,
		f: F,
		f2: impl Fn(TPayload, T::Signature) -> LocalCall,
	) -> Self::Result
	where
		F: Fn(&Account<T>) -> TPayload,
		TPayload: SignedPayload<T>;

	/// Submits an unsigned transaction onchain.
	fn submit_unsigned_transaction(
		&self,
		call: LocalCall
	) -> Option<Result<(), ()>> {
		Some(SubmitTransaction::<T, LocalCall>
			::submit_unsigned_transaction(call.into()))
	}
}

/// Utility trait to be implemented on payloads
/// that should be signed and submitted onchain.
pub trait SignedPayload<T: SigningTypes>: Encode {
	fn public(&self) -> T::Public;

	/// Sign the payload using the implementor's provided public key.
	///
	/// Returns `Some(signature)` if public key is supported.
	fn sign<C: AppCrypto<T::Public, T::Signature>>(&self) -> Option<T::Signature> {
		self.using_encoded(|payload| C::sign(payload, self.public()))
	}

	/// Verify signature against payload.
	///
	/// Returns a bool indicating whether the signature is valid or not.
	fn verify<C: AppCrypto<T::Public, T::Signature>>(&self, signature: T::Signature) -> bool {
		self.using_encoded(|payload| C::verify(payload, self.public(), signature))
	}
}
