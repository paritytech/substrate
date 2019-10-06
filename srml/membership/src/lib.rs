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

//! # Membership Module
//!
//! Allows control of membership of a set of `AccountId`s, useful for managing membership of of a
//! collective.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use rstd::prelude::*;
use support::{
	decl_module, decl_storage, decl_event, traits::{ChangeMembers, InitializeMembers},
};
use system::ensure_root;
use sr_primitives::{traits::EnsureOrigin, weights::SimpleDispatchInfo};

pub trait Trait<I=DefaultInstance>: system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as system::Trait>::Event>;

	/// Required origin for adding a member (though can always be Root).
	type AddOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for removing a member (though can always be Root).
	type RemoveOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for adding and removing a member in a single action.
	type SwapOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for resetting membership.
	type ResetOrigin: EnsureOrigin<Self::Origin>;

	/// The receiver of the signal for when the membership has been initialized. This happens pre-
	/// genesis and will usually be the same as `MembershipChanged`. If you need to do something
	/// different on initialization, then you can change this accordingly.
	type MembershipInitialized: InitializeMembers<Self::AccountId>;

	/// The receiver of the signal for when the membership has changed.
	type MembershipChanged: ChangeMembers<Self::AccountId>;
}

decl_storage! {
	trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Membership {
		/// The current membership, stored as an ordered Vec.
		Members get(members): Vec<T::AccountId>;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(phantom): rstd::marker::PhantomData<I>;
		build(|config: &Self| {
			let mut members = config.members.clone();
			members.sort();
			T::MembershipInitialized::initialize_members(&members);
			<Members<T, I>>::put(members);
		})
	}
}

decl_event!(
	pub enum Event<T, I=DefaultInstance> where
		<T as system::Trait>::AccountId,
		<T as Trait<I>>::Event,
	{
		/// The given member was added; see the transaction for who.
		MemberAdded,
		/// The given member was removed; see the transaction for who.
		MemberRemoved,
		/// Two members were swapped; see the transaction for who.
		MembersSwapped,
		/// The membership was reset; see the transaction for who the new set is.
		MembersReset,
		/// Phantom member, never used.
		Dummy(rstd::marker::PhantomData<(AccountId, Event)>),
	}
);

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		fn deposit_event() = default;

		/// Add a member `who` to the set.
		///
		/// May only be called from `AddOrigin` or root.
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn add_member(origin, who: T::AccountId) {
			T::AddOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&who).err().ok_or("already a member")?;
			members.insert(location, who.clone());
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(&[who], &[], &members[..]);

			Self::deposit_event(RawEvent::MemberAdded);
		}

		/// Remove a member `who` from the set.
		///
		/// May only be called from `RemoveOrigin` or root.
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn remove_member(origin, who: T::AccountId) {
			T::RemoveOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&who).ok().ok_or("not a member")?;
			members.remove(location);
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(&[], &[who], &members[..]);

			Self::deposit_event(RawEvent::MemberRemoved);
		}

		/// Swap out one member `remove` for another `add`.
		///
		/// May only be called from `SwapOrigin` or root.
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn swap_member(origin, remove: T::AccountId, add: T::AccountId) {
			T::SwapOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			if remove == add { return Ok(()) }

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&remove).ok().ok_or("not a member")?;
			members[location] = add.clone();
			let _location = members.binary_search(&add).err().ok_or("already a member")?;
			members.sort();
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(
				&[add],
				&[remove],
				&members[..],
			);

			Self::deposit_event(RawEvent::MembersSwapped);
		}

		/// Change the membership to a new set, disregarding the existing membership. Be nice and
		/// pass `members` pre-sorted.
		///
		/// May only be called from `ResetOrigin` or root.
		#[weight = SimpleDispatchInfo::FixedNormal(50_000)]
		fn reset_members(origin, members: Vec<T::AccountId>) {
			T::ResetOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)
				.map_err(|_| "bad origin")?;

			let mut members = members;
			members.sort();
			<Members<T, I>>::mutate(|m| {
				T::MembershipChanged::set_members_sorted(&members[..], m);
				*m = members;
			});

			Self::deposit_event(RawEvent::MembersReset);
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::cell::RefCell;
	use support::{assert_ok, assert_noop, impl_outer_origin, parameter_types};
	use runtime_io::with_externalities;
	use primitives::{H256, Blake2Hasher};
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are requried.
	use sr_primitives::{
		Perbill, traits::{BlakeTwo256, IdentityLookup}, testing::Header
	};
	use system::EnsureSignedBy;

	impl_outer_origin! {
		pub enum Origin for Test {}
	}

	// For testing the module, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of modules we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: u32 = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type WeightMultiplierUpdate = ();
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
	}
	parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
		pub const Four: u64 = 4;
		pub const Five: u64 = 5;
	}

	thread_local! {
		static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
	}

	pub struct TestChangeMembers;
	impl ChangeMembers<u64> for TestChangeMembers {
		fn change_members_sorted(incoming: &[u64], outgoing: &[u64], new: &[u64]) {
			let mut old_plus_incoming = MEMBERS.with(|m| m.borrow().to_vec());
			old_plus_incoming.extend_from_slice(incoming);
			old_plus_incoming.sort();
			let mut new_plus_outgoing = new.to_vec();
			new_plus_outgoing.extend_from_slice(outgoing);
			new_plus_outgoing.sort();
			assert_eq!(old_plus_incoming, new_plus_outgoing);

			MEMBERS.with(|m| *m.borrow_mut() = new.to_vec());
		}
	}
	impl InitializeMembers<u64> for TestChangeMembers {
		fn initialize_members(members: &[u64]) {
			MEMBERS.with(|m| *m.borrow_mut() = members.to_vec());
		}
	}

	impl Trait for Test {
		type Event = ();
		type AddOrigin = EnsureSignedBy<One, u64>;
		type RemoveOrigin = EnsureSignedBy<Two, u64>;
		type SwapOrigin = EnsureSignedBy<Three, u64>;
		type ResetOrigin = EnsureSignedBy<Four, u64>;
		type MembershipInitialized = TestChangeMembers;
		type MembershipChanged = TestChangeMembers;
	}

	type Membership = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		GenesisConfig::<Test>{
			members: vec![10, 20, 30],
			.. Default::default()
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn query_membership_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Membership::members(), vec![10, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), vec![10, 20, 30]);
		});
	}

	#[test]
	fn add_member_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::add_member(Origin::signed(5), 15), "bad origin");
			assert_noop!(Membership::add_member(Origin::signed(1), 10), "already a member");
			assert_ok!(Membership::add_member(Origin::signed(1), 15));
			assert_eq!(Membership::members(), vec![10, 15, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn remove_member_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::remove_member(Origin::signed(5), 20), "bad origin");
			assert_noop!(Membership::remove_member(Origin::signed(2), 15), "not a member");
			assert_ok!(Membership::remove_member(Origin::signed(2), 20));
			assert_eq!(Membership::members(), vec![10, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn swap_member_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::swap_member(Origin::signed(5), 10, 25), "bad origin");
			assert_noop!(Membership::swap_member(Origin::signed(3), 15, 25), "not a member");
			assert_noop!(Membership::swap_member(Origin::signed(3), 10, 30), "already a member");
			assert_ok!(Membership::swap_member(Origin::signed(3), 20, 20));
			assert_eq!(Membership::members(), vec![10, 20, 30]);
			assert_ok!(Membership::swap_member(Origin::signed(3), 10, 25));
			assert_eq!(Membership::members(), vec![20, 25, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn reset_members_works() {
		with_externalities(&mut new_test_ext(), || {
			assert_noop!(Membership::reset_members(Origin::signed(1), vec![20, 40, 30]), "bad origin");
			assert_ok!(Membership::reset_members(Origin::signed(4), vec![20, 40, 30]));
			assert_eq!(Membership::members(), vec![20, 30, 40]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}
}
