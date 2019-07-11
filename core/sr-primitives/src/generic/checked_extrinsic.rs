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
use crate::traits::{self, Member, SimpleArithmetic, MaybeDisplay, SignedExtension, DispatchError};
use crate::weights::{Weighable, Weight};

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedExtrinsic<AccountId, Index, Call, Extra> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Index, Extra)>,

	/// The function that should be called.
	pub function: Call,
}

impl<AccountId, Index, Call, Extra> traits::Applyable
for
	CheckedExtrinsic<AccountId, Index, Call, Extra>
where
	AccountId: Member + MaybeDisplay,
	Index: Member + MaybeDisplay + SimpleArithmetic,
	Call: Member,
	Extra: SignedExtension<AccountId=AccountId, Index=Index, Call=Call>,
{
	type AccountId = AccountId;
	type Call = Call;
	type Index = Index;

	fn index(&self) -> Option<&Self::Index> {
		self.signed.as_ref().map(|x| &x.1)
	}

	fn sender(&self) -> Option<&Self::AccountId> {
		self.signed.as_ref().map(|x| &x.0)
	}

	fn deconstruct(self) -> (Self::Call, Option<Self::AccountId>) {
		if let Some((id, _, extra)) = self.signed {
			(self.function, Some(id))
		} else {
			(self.function, None)
		}
	}

	fn pre_dispatch(self,
		weight: crate::weights::Weight,
	) -> Result<(Self::Call, Option<Self::AccountId>), DispatchError> {
		if let Some((id, index, extra)) = self.signed {
			Extra::pre_dispatch(extra, &id, &index, &self.function, weight)?;
			Ok((self.function, Some(id)))
		} else {
			Ok((self.function, None))
		}
	}
}

impl<AccountId, Index, Call, Extra> Weighable for CheckedExtrinsic<AccountId, Index, Call, Extra>
where
	Call: Weighable,
{
	fn weight(&self, len: usize) -> Weight {
		self.function.weight(len)
	}
}
