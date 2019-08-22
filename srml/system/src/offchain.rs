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

use sr_primitives::traits::Extrinsic as ExtrinsicT;

/// A trait responsible for producing signature payload for an extrinsic.
pub trait Signer<T: crate::Trait, Extrinsic: ExtrinsicT> {
	fn sign(
		account: T::AccountId,
		nonce: T::Index,
		call: &Extrinsic::Call,
	) -> Option<Extrinsic::SignaturePayload>;
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
		let signature_data = Self::Sign::sign(id, expected, &call).ok_or(())?;
		let xt = Self::Extrinsic::new(call, Some(signature_data)).ok_or(())?;
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

