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

use rstd::marker::{Sync, Send}; // TODO: what the fucking hell.
use crate::traits::{self, Member, SimpleArithmetic, MaybeDisplay};
use crate::weights::{Weighable, Weight};
use super::Tip;

/// Definition of something that the external world might want to say; its
/// existence implies that it has been checked and is good, particularly with
/// regards to the signature.
#[derive(PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct CheckedExtrinsic<AccountId, Index, Call, Balance> {
	/// Who this purports to be from and the number of extrinsics have come before
	/// from the same signer, if anyone (note this is not a signature).
	pub signed: Option<(AccountId, Index)>,
	/// The function that should be called.
	pub function: Call,
	/// The tip for this transaction
	pub tip: Tip<Balance>,
}

impl<AccountId, Index, Call, Balance> traits::Applyable for CheckedExtrinsic<AccountId, Index, Call, Balance>
where
	AccountId: Member + MaybeDisplay,
	Index: Member + MaybeDisplay + SimpleArithmetic,
	Call: Member,
	Balance: Sync + Send,
{
	type Index = Index;
	type AccountId = AccountId;
	type Call = Call;

	fn index(&self) -> Option<&Self::Index> {
		self.signed.as_ref().map(|x| &x.1)
	}

	fn sender(&self) -> Option<&Self::AccountId> {
		self.signed.as_ref().map(|x| &x.0)
	}

	fn deconstruct(self) -> (Self::Call, Option<Self::AccountId>) {
		(self.function, self.signed.map(|x| x.0))
	}
}

impl<AccountId, Index, Call, Balance> Weighable
	for CheckedExtrinsic<AccountId, Index, Call, Balance>
where
	Call: Weighable,
{
	fn weight(&self, len: usize) -> Weight {
		self.function.weight(len)
	}
}
