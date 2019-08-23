// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Module helpers for offchain calls.

use codec::{Encode, Codec};
use sr_primitives::app_crypto::RuntimeAppPublic;
use sr_primitives::generic::{UncheckedExtrinsic, SignedPayload};
use sr_primitives::traits::{Extrinsic as ExtrinsicT, SignedExtension, StaticLookup, MaybeDebug};

/// A trait responsible for producing signature payload for an extrinsic.
pub trait Signer<T: crate::Trait, Extrinsic: ExtrinsicT> {
	fn sign(
		account: T::AccountId,
		nonce: T::Index,
		call: Extrinsic::Call,
	) -> (Extrinsic::Call, Option<Extrinsic::SignaturePayload>);
}

pub trait GetPayload<Call, Index, Payload> {
	fn get_payload(call: Call, index: Index) -> Payload;
}

impl<T, L, P, TSigner, Address, Call, Extra, Signature> Signer<T, UncheckedExtrinsic<Address, Call, Signature, Extra>>
	for (TSigner, UncheckedExtrinsic<Address, Call, Signature, Extra>, L, P)
where
	TSigner: RuntimeAppPublic + From<T::AccountId>,
	TSigner::Signature: Into<Signature>,
	Address: Codec + Clone + PartialEq + MaybeDebug,
	Call: Encode,
	T: crate::Trait,
	Extra: SignedExtension,
	L: StaticLookup<Source=Address, Target=T::AccountId>,
	P: GetPayload<Call, T::Index, SignedPayload<Call, Extra>>,
{
	fn sign(
		account: T::AccountId,
		nonce: T::Index,
		call: Call,
	) -> (Call, Option<
		<UncheckedExtrinsic<Address, Call, Signature, Extra> as ExtrinsicT>::SignaturePayload
	>) {
		let raw_payload = P::get_payload(call, nonce);
		let signature = raw_payload.using_encoded(|payload| {
			TSigner::from(account.clone()).sign(&payload)
		});
		let address = L::unlookup(account);
		let (call, extra, _) = raw_payload.deconstruct();
		match signature {
			Some(sig) => (call, Some((address, sig.into(), extra))),
			None => (call, None),
		}
	}
}

/// A trait to sign and submit transactions in offchain calls.
pub trait SubmitSignedTransaction<T: crate::Trait, Call> {
	/// Unchecked extrinsic type.
	type Extrinsic: ExtrinsicT<Call=Call> + codec::Encode;

	/// A runtime-specific function to sign and produce signature payload for extrinsic.
	type Sign: Signer<T, Self::Extrinsic>;

	/// Sign given call and submit it to the transaction pool.
	///
	/// Returns `Ok` if the transaction was submitted correctly
	/// and `Err` if the key for given `id` was not found or the
	/// transaction was rejected from the pool.
	fn sign_and_submit(call: impl Into<Call>, id: T::AccountId) -> Result<(), ()> {
		let call = call.into();
		let expected = <crate::Module<T>>::account_nonce(&id);
		let (call, signature_data) = Self::Sign::sign(id, expected, call);
		// return an error if there is no signature_data, instead of producing unsigned extrinsic.
		let signature_data = Some(signature_data.ok_or(())?);
		let xt = Self::Extrinsic::new(call, signature_data).ok_or(())?;
		runtime_io::submit_transaction(&xt)
	}
}

/// A trait to submit unsigned transactions in offchain calls.
pub trait SubmitUnsignedTransaction<T: crate::Trait, Call> {
	/// Unchecked extrinsic type.
	type Extrinsic: ExtrinsicT<Call=Call> + codec::Encode;


	/// Submit given call to the transaction pool as unsigned transaction.
	///
	/// Returns `Ok` if the transaction was submitted correctly
	/// and `Err` if transaction was rejected from the pool.
	fn submit_unsigned(call: impl Into<Call>) -> Result<(), ()> {
		let xt = Self::Extrinsic::new(call.into(), None).ok_or(())?;
		runtime_io::submit_transaction(&xt)
	}
}

/// A default type used to submit transactions to the pool.
pub struct TransactionSubmitter<S, E> {
	_signer: rstd::marker::PhantomData<(S, E)>,
}

impl<S, E> Default for TransactionSubmitter<S, E> {
	fn default() -> Self {
		Self {
			_signer: Default::default(),
		}
	}
}

/// A blanket implementation to simplify creation of transaction signer & submitter in the runtime.
impl<T, E, S, C> SubmitSignedTransaction<T, C> for TransactionSubmitter<S, E> where
	T: crate::Trait,
	S: Signer<T, E>,
	E: ExtrinsicT<Call=C> + codec::Encode,
{
	type Extrinsic = E;
	type Sign = S;
}

/// A blanket impl to use the same submitter for usigned transactions as well.
impl<T, E, S, C> SubmitUnsignedTransaction<T, C> for TransactionSubmitter<S, E> where
	T: crate::Trait,
	E: ExtrinsicT<Call=C> + codec::Encode,
{
	type Extrinsic = E;
}

