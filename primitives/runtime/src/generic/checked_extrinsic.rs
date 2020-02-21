// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Generic implementation of an extrinsic that has passed the verification
//! stage.

use crate::traits::{
	self, Member, MaybeDisplay, SignedExtension, Dispatchable,
};
use crate::traits::ValidateUnsigned;
use crate::transaction_validity::TransactionValidity;

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone, sp_core::RuntimeDebug)]
pub struct CheckedExtrinsic<AccountId, Call, Extra> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Extra)>,

	/// The function that should be called.
	pub function: Call,
}

impl<AccountId, Call, Extra, Origin, Info> traits::Applyable for
	CheckedExtrinsic<AccountId, Call, Extra>
where
	AccountId: Member + MaybeDisplay,
	Call: Member + Dispatchable<Origin=Origin>,
	Extra: SignedExtension<AccountId=AccountId, Call=Call, DispatchInfo=Info>,
	Origin: From<Option<AccountId>>,
	Info: Clone,
{
	type AccountId = AccountId;
	type Call = Call;
	type DispatchInfo = Info;

	fn sender(&self) -> Option<&Self::AccountId> {
		self.signed.as_ref().map(|x| &x.0)
	}

	fn validate<U: ValidateUnsigned<Call = Self::Call>>(
		&self,
		info: Self::DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		if let Some((ref id, ref extra)) = self.signed {
			Extra::validate(extra, id, &self.function, info.clone(), len)
		} else {
			let valid = Extra::validate_unsigned(&self.function, info, len)?;
			let unsigned_validation = U::validate_unsigned(&self.function)?;
			Ok(valid.combine_with(unsigned_validation))
		}
	}

	fn apply<U: ValidateUnsigned<Call=Self::Call>>(
		self,
		info: Self::DispatchInfo,
		len: usize,
	) -> crate::ApplyExtrinsicResult {
		let (maybe_who, pre) = if let Some((id, extra)) = self.signed {
			let pre = Extra::pre_dispatch(extra, &id, &self.function, info.clone(), len)?;
			(Some(id), pre)
		} else {
			let pre = Extra::pre_dispatch_unsigned(&self.function, info.clone(), len)?;
			U::pre_dispatch(&self.function)?;
			(None, pre)
		};
		let res = self.function.dispatch(Origin::from(maybe_who));
		Extra::post_dispatch(pre, info.clone(), len);
		Ok(res.map_err(Into::into))
	}
}
