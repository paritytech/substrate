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

use codec::Encode;
use sr_primitives::app_crypto::RuntimeAppPublic;
use sr_primitives::traits::Extrinsic as ExtrinsicT;

/// A trait responsible for signing a payload using given account.
pub trait Signer<Public, Signature> {
	/// Sign any encodable payload with given account and produce a signature.
	///
	/// Returns `Some` if signing succeeded and `None` in case the `account` couldn't be used.
	fn sign<Payload: Encode>(public: Public, payload: &Payload) -> Option<Signature>;
}

impl<Public, Signature, AppPublic> Signer<Public, Signature> for AppPublic where
	AppPublic: RuntimeAppPublic + From<Public>,
	AppPublic::Signature: Into<Signature>,
{
	fn sign<Payload: Encode>(public: Public, raw_payload: &Payload) -> Option<Signature> {
		raw_payload.using_encoded(|payload| {
			AppPublic::from(public).sign(&payload).map(Into::into)
		})
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
		runtime_io::submit_transaction(xt.encode())
	}
}

/// A default type used to submit transactions to the pool.
pub struct TransactionSubmitter<S, C, E> {
	_signer: rstd::marker::PhantomData<(S, C, E)>,
}

impl<S, C, E> Default for TransactionSubmitter<S, C, E> {
	fn default() -> Self {
		Self {
			_signer: Default::default(),
		}
	}
}

/// A blanket impl to use the same submitter for usigned transactions as well.
impl<T, E, S, C, Call> SubmitUnsignedTransaction<T, Call> for TransactionSubmitter<S, C, E> where
	T: crate::Trait,
	E: ExtrinsicT<Call=Call> + codec::Encode,
{
	type Extrinsic = E;
}
