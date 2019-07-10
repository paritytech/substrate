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

use crate::traits::{self, Member, SimpleArithmetic, MaybeDisplay};
use crate::weights::{Weighable, Weight};
use crate::generic::tip::{Tip, Tippable};

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
	/// An optional tip value that may or may not exist based on the underlying unchecked extrinsic.
	///
	/// Most often this is:
	/// - `None` if the unchecked extrinsic does not have a tip OR it is unsigned.
	/// - `Some` if the opposite.
	pub tip: Option<Tip<Balance>>,
}

impl<AccountId, Index, Call, Balance> traits::Applyable for CheckedExtrinsic<AccountId, Index, Call, Balance>
where
	AccountId: Member + MaybeDisplay,
	Index: Member + MaybeDisplay + SimpleArithmetic,
	Call: Member,
	Balance: Member,
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

impl<AccountId, Index, Call, Balance> Weighable for CheckedExtrinsic<AccountId, Index, Call, Balance>
where
	Call: Weighable,
{
	fn weight(&self, len: usize) -> Weight {
		self.function.weight(len)
	}
}

/// `ExtBalance` is the balance type fed by the `check()` implementation of various unchecked
/// extrinsics. `NodeBalance` is the actual balance type used as a primitive type of the substrate
/// node.
///
/// In practice, if they underlying unchecked transaction is tip-aware, they are the same. Otherwise,
/// the tip is always `None` and the type is of no importance.
impl<AccountId, Index, Call, ExtBalance, NodeBalance> Tippable<NodeBalance>
	for CheckedExtrinsic<AccountId, Index, Call, ExtBalance>
where
	ExtBalance: Clone + Copy,
	NodeBalance: From<ExtBalance>,
{
	fn tip(&self) -> Option<Tip<NodeBalance>> {
		// This is a hacky way to prevent `unchecked_mortal[_compact]_extrinsic` types, which
		// don't have a tip, become generic over a balance type.
		// Basically, this CheckedExtrinsic is built either 1- from an
		// `UncheckedMortalCompactTippedExtrinsic`, which is tip-aware and hence, the second arm
		// will be trivially executed and the type conversion will be safe (the compiler is probably
		// smart enough to remove it in fact). In this case, NodeBalance and ExtBalance are the same.
		// Or 2- this is built from all other types of uncheckedextrinsic which do not have tip and
		// hence are not tip-aware. These modules will naively place a u32 (can be `()` in practice)
		// as the type and it does not matter since `None` is used in this case (first arm).
		match &self.tip {
			None => None,
			Some(Tip::Sender(v)) => Some(Tip::Sender(NodeBalance::from(*v))),
		}
	}
}
