// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use rstd::result::Result;
use crate::traits::{
	self, Member, MaybeDisplay, SignedExtension, DispatchError, Dispatchable, DispatchResult,
	ValidateUnsigned
};
use crate::weights::{GetDispatchInfo, DispatchInfo};
use crate::transaction_validity::TransactionValidity;

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedExtrinsic<AccountId, Call, Extra> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Extra)>,

	/// The function that should be called.
	pub function: Call,
}

impl<AccountId, Call, Extra, Origin> traits::Applyable
for
	CheckedExtrinsic<AccountId, Call, Extra>
where
	AccountId: Member + MaybeDisplay,
	Call: Member + Dispatchable<Origin=Origin>,
	Extra: SignedExtension<AccountId=AccountId>,
	Origin: From<Option<AccountId>>,
{
	type AccountId = AccountId;

	type Call = Call;

	fn sender(&self) -> Option<&Self::AccountId> {
		self.signed.as_ref().map(|x| &x.0)
	}

	fn validate<U: ValidateUnsigned<Call=Self::Call>>(&self,
		info: DispatchInfo,
		len: usize,
	) -> TransactionValidity {
		if let Some((ref id, ref extra)) = self.signed {
			Extra::validate(extra, id, info, len).into()
		} else {
			match Extra::validate_unsigned(info, len) {
				Ok(extra) => match U::validate_unsigned(&self.function) {
					TransactionValidity::Valid(v) =>
						TransactionValidity::Valid(v.combine_with(extra)),
					x => x,
				},
				x => x.into(),
			}
		}
	}

	fn dispatch(self,
		info: DispatchInfo,
		len: usize,
	) -> Result<DispatchResult, DispatchError> {
		let maybe_who = if let Some((id, extra)) = self.signed {
			Extra::pre_dispatch(extra, &id, info, len)?;
			Some(id)
		} else {
			Extra::pre_dispatch_unsigned(info, len)?;
			None
		};
		Ok(self.function.dispatch(Origin::from(maybe_who)))
	}
}

impl<AccountId, Call, Extra> GetDispatchInfo for CheckedExtrinsic<AccountId, Call, Extra>
where
	Call: GetDispatchInfo,
{
	fn get_dispatch_info(&self) -> DispatchInfo {
		self.function.get_dispatch_info()
	}
}
