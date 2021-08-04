// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Traits for dealing with the idea of membership.

use sp_std::{marker::PhantomData, prelude::*};

/// A trait for querying whether a type can be said to "contain" a value.
pub trait Contains<T> {
	/// Return `true` if this "contains" the given value `t`.
	fn contains(t: &T) -> bool;
}

/// A `Contains` implementation which always returns `true`.
pub struct All<T>(PhantomData<T>);
impl<T> Contains<T> for All<T> {
	fn contains(_: &T) -> bool {
		true
	}
}

#[impl_trait_for_tuples::impl_for_tuples(30)]
impl<T> Contains<T> for Tuple {
	fn contains(t: &T) -> bool {
		for_tuples!( #(
			if Tuple::contains(t) { return true }
		)* );
		false
	}
}

/// Create a type which implements the `Contains` trait for a particular type with syntax similar
/// to `matches!`.
#[macro_export]
macro_rules! match_type {
	( pub type $n:ident: impl Contains<$t:ty> = { $phead:pat $( | $ptail:pat )* } ; ) => {
		pub struct $n;
		impl $crate::traits::Contains<$t> for $n {
			fn contains(l: &$t) -> bool {
				matches!(l, $phead $( | $ptail )* )
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	match_type! {
		pub type OneOrTenToTwenty: impl Contains<u8> = { 1 | 10..=20 };
	}

	#[test]
	fn match_type_works() {
		for i in 0..=255 {
			assert_eq!(OneOrTenToTwenty::contains(&i), i == 1 || i >= 10 && i <= 20);
		}
	}
}

/// A trait for a set which can enumerate its members in order.
pub trait SortedMembers<T: Ord> {
	/// Get a vector of all members in the set, ordered.
	fn sorted_members() -> Vec<T>;

	/// Return `true` if this "contains" the given value `t`.
	fn contains(t: &T) -> bool {
		Self::sorted_members().binary_search(t).is_ok()
	}

	/// Get the number of items in the set.
	fn count() -> usize {
		Self::sorted_members().len()
	}

	/// Add an item that would satisfy `contains`. It does not make sure any other
	/// state is correctly maintained or generated.
	///
	/// **Should be used for benchmarking only!!!**
	#[cfg(feature = "runtime-benchmarks")]
	fn add(_t: &T) {
		unimplemented!()
	}
}

/// Adapter struct for turning an `OrderedMembership` impl into a `Contains` impl.
pub struct AsContains<OM>(PhantomData<(OM,)>);
impl<T: Ord + Eq, OM: SortedMembers<T>> Contains<T> for AsContains<OM> {
	fn contains(t: &T) -> bool {
		OM::contains(t)
	}
}

/// Trivial utility for implementing `Contains`/`OrderedMembership` with a `Vec`.
pub struct IsInVec<T>(PhantomData<T>);
impl<X: Eq, T: super::Get<Vec<X>>> Contains<X> for IsInVec<T> {
	fn contains(t: &X) -> bool {
		T::get().contains(t)
	}
}
impl<X: Ord + PartialOrd, T: super::Get<Vec<X>>> SortedMembers<X> for IsInVec<T> {
	fn sorted_members() -> Vec<X> {
		let mut r = T::get();
		r.sort();
		r
	}
}

/// A trait for querying bound for the length of an implementation of `Contains`
pub trait ContainsLengthBound {
	/// Minimum number of elements contained
	fn min_len() -> usize;
	/// Maximum number of elements contained
	fn max_len() -> usize;
}

/// Trait for type that can handle the initialization of account IDs at genesis.
pub trait InitializeMembers<AccountId> {
	/// Initialize the members to the given `members`.
	fn initialize_members(members: &[AccountId]);
}

impl<T> InitializeMembers<T> for () {
	fn initialize_members(_: &[T]) {}
}

/// Trait for type that can handle incremental changes to a set of account IDs.
pub trait ChangeMembers<AccountId: Clone + Ord> {
	/// A number of members `incoming` just joined the set and replaced some `outgoing` ones. The
	/// new set is given by `new`, and need not be sorted.
	///
	/// This resets any previous value of prime.
	fn change_members(incoming: &[AccountId], outgoing: &[AccountId], mut new: Vec<AccountId>) {
		new.sort();
		Self::change_members_sorted(incoming, outgoing, &new[..]);
	}

	/// A number of members `_incoming` just joined the set and replaced some `_outgoing` ones. The
	/// new set is thus given by `sorted_new` and **must be sorted**.
	///
	/// NOTE: This is the only function that needs to be implemented in `ChangeMembers`.
	///
	/// This resets any previous value of prime.
	fn change_members_sorted(
		incoming: &[AccountId],
		outgoing: &[AccountId],
		sorted_new: &[AccountId],
	);

	/// Set the new members; they **must already be sorted**. This will compute the diff and use it to
	/// call `change_members_sorted`.
	///
	/// This resets any previous value of prime.
	fn set_members_sorted(new_members: &[AccountId], old_members: &[AccountId]) {
		let (incoming, outgoing) = Self::compute_members_diff_sorted(new_members, old_members);
		Self::change_members_sorted(&incoming[..], &outgoing[..], &new_members);
	}

	/// Compute diff between new and old members; they **must already be sorted**.
	///
	/// Returns incoming and outgoing members.
	fn compute_members_diff_sorted(
		new_members: &[AccountId],
		old_members: &[AccountId],
	) -> (Vec<AccountId>, Vec<AccountId>) {
		let mut old_iter = old_members.iter();
		let mut new_iter = new_members.iter();
		let mut incoming = Vec::new();
		let mut outgoing = Vec::new();
		let mut old_i = old_iter.next();
		let mut new_i = new_iter.next();
		loop {
			match (old_i, new_i) {
				(None, None) => break,
				(Some(old), Some(new)) if old == new => {
					old_i = old_iter.next();
					new_i = new_iter.next();
				},
				(Some(old), Some(new)) if old < new => {
					outgoing.push(old.clone());
					old_i = old_iter.next();
				},
				(Some(old), None) => {
					outgoing.push(old.clone());
					old_i = old_iter.next();
				},
				(_, Some(new)) => {
					incoming.push(new.clone());
					new_i = new_iter.next();
				},
			}
		}
		(incoming, outgoing)
	}

	/// Set the prime member.
	fn set_prime(_prime: Option<AccountId>) {}

	/// Get the current prime.
	fn get_prime() -> Option<AccountId> {
		None
	}
}

impl<T: Clone + Ord> ChangeMembers<T> for () {
	fn change_members(_: &[T], _: &[T], _: Vec<T>) {}
	fn change_members_sorted(_: &[T], _: &[T], _: &[T]) {}
	fn set_members_sorted(_: &[T], _: &[T]) {}
	fn set_prime(_: Option<T>) {}
}
