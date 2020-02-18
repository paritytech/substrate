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

use codec::Encode;
use sp_std::convert::TryInto;
use sp_std::prelude::Vec;
use sp_runtime::app_crypto::{RuntimeAppPublic, AppPublic, AppSignature};
use sp_runtime::traits::{Extrinsic as ExtrinsicT, IdentifyAccount, One};
use frame_support::{debug, storage::StorageMap};

/// Creates runtime-specific signed transaction.
///
/// This trait should be implemented by your `Runtime` to be able
/// to submit `SignedTransaction`s` to the pool from off-chain code.
pub trait CreateTransaction<T: crate::Trait, Extrinsic: ExtrinsicT> {
	/// A `Public` key representing a particular `AccountId`.
	type Public: IdentifyAccount<AccountId=T::AccountId> + Clone;
	/// A `Signature` generated by the `Signer`.
	type Signature;

	/// Attempt to create signed extrinsic data that encodes call from given account.
	///
	/// Runtime implementation is free to construct the payload to sign and the signature
	/// in any way it wants.
	/// Returns `None` if signed extrinsic could not be created (either because signing failed
	/// or because of any other runtime-specific reason).
	fn create_transaction<F: Signer<Self::Public, Self::Signature>>(
		call: Extrinsic::Call,
		public: Self::Public,
		account: T::AccountId,
		nonce: T::Index,
	) -> Option<(Extrinsic::Call, Extrinsic::SignaturePayload)>;
}

/// A trait responsible for signing a payload using given account.
///
/// This trait is usually going to represent a local public key
/// that has ability to sign arbitrary `Payloads`.
///
/// NOTE: Most likely you don't need to implement this trait manually.
/// It has a blanket implementation for all `RuntimeAppPublic` types,
/// so it's enough to pass an application-specific crypto type.
///
/// To easily create `SignedTransaction`s have a look at the
/// [`TransactionSubmitter`] type.
pub trait Signer<Public, Signature> {
	/// Sign any encodable payload with given account and produce a signature.
	///
	/// Returns `Some` if signing succeeded and `None` in case the `account` couldn't
	/// be used (for instance we couldn't convert it to required application specific crypto).
	fn sign<Payload: Encode>(public: Public, payload: &Payload) -> Option<Signature>;
}

/// A `Signer` implementation for any `AppPublic` type.
///
/// This implementation additionally supports conversion to/from multi-signature/multi-signer
/// wrappers.
/// If the wrapped crypto doesn't match `AppPublic`s crypto `None` is returned.
impl<Public, Signature, TAnyAppPublic> Signer<Public, Signature> for TAnyAppPublic where
	TAnyAppPublic: RuntimeAppPublic
		+ AppPublic
		+ From<<TAnyAppPublic as AppPublic>::Generic>,
	<TAnyAppPublic as RuntimeAppPublic>::Signature: AppSignature,
	Signature: From<
		<<TAnyAppPublic as RuntimeAppPublic>::Signature as AppSignature>::Generic
	>,
	Public: TryInto<<TAnyAppPublic as AppPublic>::Generic>
{
	fn sign<Payload: Encode>(public: Public, raw_payload: &Payload) -> Option<Signature> {
		raw_payload.using_encoded(|payload| {
			let public = public.try_into().ok()?;
			TAnyAppPublic::from(public).sign(&payload)
				.map(
					<<TAnyAppPublic as RuntimeAppPublic>::Signature as AppSignature>
					 ::Generic::from
				)
				.map(Signature::from)
		})
	}
}

/// Retrieves a public key type for given `SignAndSubmitTransaction`.
pub type PublicOf<T, Call, X> = <
	<X as SignAndSubmitTransaction<T, Call>>::CreateTransaction
	as
	CreateTransaction<T, <X as SignAndSubmitTransaction<T, Call>>::Extrinsic>
>::Public;

/// A trait to sign and submit transactions in off-chain calls.
///
/// NOTE: Most likely you should not implement this trait yourself.
/// There is an implementation for
/// [`TransactionSubmitter`] type, which
/// you should use.
pub trait SignAndSubmitTransaction<T: crate::Trait, Call> {
	/// Unchecked extrinsic type.
	type Extrinsic: ExtrinsicT<Call=Call> + codec::Encode;

	/// A runtime-specific type to produce signed data for the extrinsic.
	type CreateTransaction: CreateTransaction<T, Self::Extrinsic>;

	/// A type used to sign transactions created using `CreateTransaction`.
	type Signer: Signer<
		PublicOf<T, Call, Self>,
		<Self::CreateTransaction as CreateTransaction<T, Self::Extrinsic>>::Signature,
	>;

	/// Sign given call and submit it to the transaction pool.
	///
	/// Returns `Ok` if the transaction was submitted correctly
	/// and `Err` if the key for given `id` was not found or the
	/// transaction was rejected from the pool.
	fn sign_and_submit(call: impl Into<Call>, public: PublicOf<T, Call, Self>) -> Result<(), ()> {
		let call = call.into();
		let id = public.clone().into_account();
		let (expected_nonce, extra) = super::Account::<T>::get(&id);
		debug::native::debug!(
			target: "offchain",
			"Creating signed transaction from account: {:?} (nonce: {:?})",
			id,
			expected_nonce,
		);
		let (call, signature_data) = Self::CreateTransaction
			::create_transaction::<Self::Signer>(call, public, id.clone(), expected_nonce)
			.ok_or(())?;
		// increment the nonce. This is fine, since the code should always
		// be running in off-chain context, so we NEVER persists data.
		super::Account::<T>::insert(&id, (expected_nonce + One::one(), extra));

		let xt = Self::Extrinsic::new(call, Some(signature_data)).ok_or(())?;
		sp_io::offchain::submit_transaction(xt.encode())
	}
}

/// A trait to submit unsigned transactions in off-chain calls.
///
/// NOTE: Most likely you should not implement this trait yourself.
/// There is an implementation for
/// [`TransactionSubmitter`] type, which
/// you should use.
pub trait SubmitUnsignedTransaction<T: crate::Trait, Call> {
	/// Unchecked extrinsic type.
	type Extrinsic: ExtrinsicT<Call=Call> + codec::Encode;

	/// Submit given call to the transaction pool as unsigned transaction.
	///
	/// Returns `Ok` if the transaction was submitted correctly
	/// and `Err` if transaction was rejected from the pool.
	fn submit_unsigned(call: impl Into<Call>) -> Result<(), ()> {
		let xt = Self::Extrinsic::new(call.into(), None).ok_or(())?;
		sp_io::offchain::submit_transaction(xt.encode())
	}
}

/// A utility trait to easily create signed transactions
/// from accounts in node's local keystore.
///
/// NOTE: Most likely you should not implement this trait yourself.
/// There is an implementation for
/// [`TransactionSubmitter`] type, which
/// you should use.
pub trait SubmitSignedTransaction<T: crate::Trait, Call> {
	/// A `SignAndSubmitTransaction` implementation.
	type SignAndSubmit: SignAndSubmitTransaction<T, Call>;

	/// Find local keys that match given list of accounts.
	///
	/// Technically it finds an intersection between given list of `AccountId`s
	/// and accounts that are represented by public keys in local keystore.
	/// If `None` is passed it returns all accounts in the keystore.
	///
	/// Returns both public keys and `AccountId`s of accounts that are available.
	/// Such accounts can later be used to sign a payload or send signed transactions.
	fn find_local_keys(accounts: Option<impl IntoIterator<Item = T::AccountId>>) -> Vec<(
		T::AccountId,
		PublicOf<T, Call, Self::SignAndSubmit>,
	)>;

	/// Find all available local keys.
	///
	/// This is equivalent of calling `find_local_keys(None)`.
	fn find_all_local_keys() -> Vec<(T::AccountId, PublicOf<T, Call, Self::SignAndSubmit>)> {
		Self::find_local_keys(None as Option<Vec<_>>)
	}

	/// Check if there are keys for any of given accounts that could be used to send a transaction.
	///
	/// This check can be used as an early-exit condition to avoid doing too
	/// much work, before we actually realise that there are no accounts that you
	/// we could use for signing.
	fn can_sign_with(accounts: Option<impl IntoIterator<Item = T::AccountId>>) -> bool {
		!Self::find_local_keys(accounts).is_empty()
	}

	/// Check if there are any keys that could be used for signing.
	///
	/// This is equivalent of calling `can_sign_with(None)`.
	fn can_sign() -> bool {
		Self::can_sign_with(None as Option<Vec<_>>)
	}

	/// Create and submit signed transactions from supported accounts.
	///
	/// This method should intersect given list of accounts with the ones
	/// supported locally and submit signed transaction containing given `Call`
	/// with every of them.
	///
	/// Returns a vector of results and account ids that were supported.
	#[must_use]
	fn submit_signed_from(
		call: impl Into<Call> + Clone,
		accounts: impl IntoIterator<Item = T::AccountId>,
	) -> Vec<(T::AccountId, Result<(), ()>)> {
		let keys = Self::find_local_keys(Some(accounts));
		keys.into_iter().map(|(account, pub_key)| {
			let call = call.clone().into();
			(
				account,
				Self::SignAndSubmit::sign_and_submit(call, pub_key)
			)
		}).collect()
	}

	/// Create and submit signed transactions from all local accounts.
	///
	/// This method submits a signed transaction from all local accounts
	/// for given application crypto.
	///
	/// Returns a vector of results and account ids that were supported.
	#[must_use]
	fn submit_signed(
		call: impl Into<Call> + Clone,
	) -> Vec<(T::AccountId, Result<(), ()>)> {
		let keys = Self::find_all_local_keys();
		keys.into_iter().map(|(account, pub_key)| {
			let call = call.clone().into();
			(
				account,
				Self::SignAndSubmit::sign_and_submit(call, pub_key)
			)
		}).collect()
	}
}

/// A default type used to submit transactions to the pool.
///
/// This is passed into each runtime as an opaque associated type that can have either of:
/// - [`SignAndSubmitTransaction`]
/// - [`SubmitUnsignedTransaction`]
/// - [`SubmitSignedTransaction`]
/// and used accordingly.
///
/// This struct should be constructed by providing the following generic parameters:
/// * `Signer` - Usually the application specific key type (see `app_crypto`).
/// * `CreateTransaction` - A type that is able to produce signed transactions,
///		usually it's going to be the entire `Runtime` object.
/// * `Extrinsic` - A runtime-specific type for in-block extrinsics.
///
/// If you only need the ability to submit unsigned transactions,
/// you may substitute both `Signer` and `CreateTransaction` with any type.
pub struct TransactionSubmitter<Signer, CreateTransaction, Extrinsic> {
	_signer: sp_std::marker::PhantomData<(Signer, CreateTransaction, Extrinsic)>,
}

impl<S, C, E> Default for TransactionSubmitter<S, C, E> {
	fn default() -> Self {
		Self {
			_signer: Default::default(),
		}
	}
}

/// A blanket implementation to simplify creation of transaction signer & submitter in the runtime.
impl<T, E, S, C, Call> SignAndSubmitTransaction<T, Call> for TransactionSubmitter<S, C, E> where
	T: crate::Trait,
	C: CreateTransaction<T, E>,
	S: Signer<<C as CreateTransaction<T, E>>::Public, <C as CreateTransaction<T, E>>::Signature>,
	E: ExtrinsicT<Call=Call> + codec::Encode,
{
	type Extrinsic = E;
	type CreateTransaction = C;
	type Signer = S;
}

/// A blanket implementation to use the same submitter for unsigned transactions as well.
impl<T, E, S, C, Call> SubmitUnsignedTransaction<T, Call> for TransactionSubmitter<S, C, E> where
	T: crate::Trait,
	E: ExtrinsicT<Call=Call> + codec::Encode,
{
	type Extrinsic = E;
}

/// A blanket implementation to support local keystore of application-crypto types.
impl<T, C, E, S, Call> SubmitSignedTransaction<T, Call> for TransactionSubmitter<S, C, E> where
	T: crate::Trait,
	C: CreateTransaction<T, E>,
	E: ExtrinsicT<Call=Call> + codec::Encode,
	S: Signer<<C as CreateTransaction<T, E>>::Public, <C as CreateTransaction<T, E>>::Signature>,
	// Make sure we can unwrap the app crypto key.
	S: RuntimeAppPublic + AppPublic + Into<<S as AppPublic>::Generic>,
	// Make sure we can convert from wrapped crypto to public key (e.g. `MultiSigner`)
	S::Generic: Into<PublicOf<T, Call, Self>>,
	// For simplicity we require the same trait to implement `SignAndSubmitTransaction` too.
	Self: SignAndSubmitTransaction<T, Call, Signer = S, Extrinsic = E, CreateTransaction = C>,
{
	type SignAndSubmit = Self;

	fn find_local_keys(accounts: Option<impl IntoIterator<Item = T::AccountId>>) -> Vec<(
		T::AccountId,
		PublicOf<T, Call, Self::SignAndSubmit>,
	)> {
		// Convert app-specific keys into generic ones.
		let local_accounts_and_keys = S::all()
			.into_iter()
			.map(|app_key| {
				// unwrap app-crypto
				let generic_pub_key: <S as AppPublic>::Generic = app_key.into();
				// convert to expected public key type (might be MultiSigner)
				let signer_pub_key: PublicOf<T, Call, Self::SignAndSubmit> = generic_pub_key.into();
				// lookup accountid for that pubkey
				let account = signer_pub_key.clone().into_account();
				(account, signer_pub_key)
			}).collect::<Vec<_>>();

		if let Some(accounts) = accounts {
			let mut local_accounts_and_keys = local_accounts_and_keys;
			// sort by accountId to allow bin-search.
			local_accounts_and_keys.sort_by(|a, b| a.0.cmp(&b.0));

			// get all the matching accounts
			accounts.into_iter().filter_map(|acc| {
				let idx = local_accounts_and_keys.binary_search_by(|a| a.0.cmp(&acc)).ok()?;
				local_accounts_and_keys.get(idx).cloned()
			}).collect()
		} else {
			// just return all account ids and keys
			local_accounts_and_keys
		}
	}

	fn can_sign_with(accounts: Option<impl IntoIterator<Item = T::AccountId>>) -> bool {
		// early exit if we care about any account.
		if accounts.is_none() {
			!S::all().is_empty()
		} else {
			!Self::find_local_keys(accounts).is_empty()
		}
	}
}
