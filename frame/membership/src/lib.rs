// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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
//! collective. A prime member may be set.

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use sp_std::prelude::*;
use frame_support::{
	decl_module, decl_storage, decl_event, decl_error,
	traits::{ChangeMembers, InitializeMembers, EnsureOrigin},
};
use frame_system::{self as system, ensure_root, ensure_signed};

pub trait Trait<I=DefaultInstance>: frame_system::Trait {
	/// The overarching event type.
	type Event: From<Event<Self, I>> + Into<<Self as frame_system::Trait>::Event>;

	/// Required origin for adding a member (though can always be Root).
	type AddOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for removing a member (though can always be Root).
	type RemoveOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for adding and removing a member in a single action.
	type SwapOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for resetting membership.
	type ResetOrigin: EnsureOrigin<Self::Origin>;

	/// Required origin for setting or resetting the prime member.
	type PrimeOrigin: EnsureOrigin<Self::Origin>;

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
		Members get(fn members): Vec<T::AccountId>;

		/// The current prime member, if one exists.
		Prime get(fn prime): Option<T::AccountId>;
	}
	add_extra_genesis {
		config(members): Vec<T::AccountId>;
		config(phantom): sp_std::marker::PhantomData<I>;
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
		<T as frame_system::Trait>::AccountId,
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
		/// One of the members' keys changed.
		KeyChanged,
		/// Phantom member, never used.
		Dummy(sp_std::marker::PhantomData<(AccountId, Event)>),
	}
);

decl_error! {
	/// Error for the nicks module.
	pub enum Error for Module<T: Trait<I>, I: Instance> {
		/// Already a member.
		AlreadyMember,
		/// Not a member.
		NotMember,
	}
}

decl_module! {
	pub struct Module<T: Trait<I>, I: Instance=DefaultInstance>
		for enum Call
		where origin: T::Origin
	{
		fn deposit_event() = default;

		/// Add a member `who` to the set.
		///
		/// May only be called from `AddOrigin` or root.
		#[weight = 50_000_000]
		fn add_member(origin, who: T::AccountId) {
			T::AddOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&who).err().ok_or(Error::<T, I>::AlreadyMember)?;
			members.insert(location, who.clone());
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(&[who], &[], &members[..]);

			Self::deposit_event(RawEvent::MemberAdded);
		}

		/// Remove a member `who` from the set.
		///
		/// May only be called from `RemoveOrigin` or root.
		#[weight = 50_000_000]
		fn remove_member(origin, who: T::AccountId) {
			T::RemoveOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&who).ok().ok_or(Error::<T, I>::NotMember)?;
			members.remove(location);
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(&[], &[who], &members[..]);
			Self::rejig_prime(&members);

			Self::deposit_event(RawEvent::MemberRemoved);
		}

		/// Swap out one member `remove` for another `add`.
		///
		/// May only be called from `SwapOrigin` or root.
		///
		/// Prime membership is *not* passed from `remove` to `add`, if extant.
		#[weight = 50_000_000]
		fn swap_member(origin, remove: T::AccountId, add: T::AccountId) {
			T::SwapOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			if remove == add { return Ok(()) }

			let mut members = <Members<T, I>>::get();
			let location = members.binary_search(&remove).ok().ok_or(Error::<T, I>::NotMember)?;
			let _ = members.binary_search(&add).err().ok_or(Error::<T, I>::AlreadyMember)?;
			members[location] = add.clone();
			members.sort();
			<Members<T, I>>::put(&members);

			T::MembershipChanged::change_members_sorted(
				&[add],
				&[remove],
				&members[..],
			);
			Self::rejig_prime(&members);

			Self::deposit_event(RawEvent::MembersSwapped);
		}

		/// Change the membership to a new set, disregarding the existing membership. Be nice and
		/// pass `members` pre-sorted.
		///
		/// May only be called from `ResetOrigin` or root.
		#[weight = 50_000_000]
		fn reset_members(origin, members: Vec<T::AccountId>) {
			T::ResetOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;

			let mut members = members;
			members.sort();
			<Members<T, I>>::mutate(|m| {
				T::MembershipChanged::set_members_sorted(&members[..], m);
				Self::rejig_prime(&members);
				*m = members;
			});


			Self::deposit_event(RawEvent::MembersReset);
		}

		/// Swap out the sending member for some other key `new`.
		///
		/// May only be called from `Signed` origin of a current member.
		///
		/// Prime membership is passed from the origin account to `new`, if extant.
		#[weight = 50_000_000]
		fn change_key(origin, new: T::AccountId) {
			let remove = ensure_signed(origin)?;

			if remove != new {
				let mut members = <Members<T, I>>::get();
				let location = members.binary_search(&remove).ok().ok_or(Error::<T, I>::NotMember)?;
				let _ = members.binary_search(&new).err().ok_or(Error::<T, I>::AlreadyMember)?;
				members[location] = new.clone();
				members.sort();
				<Members<T, I>>::put(&members);

				T::MembershipChanged::change_members_sorted(
					&[new.clone()],
					&[remove.clone()],
					&members[..],
				);

				if Prime::<T, I>::get() == Some(remove) {
					Prime::<T, I>::put(&new);
					T::MembershipChanged::set_prime(Some(new));
				}
			}

			Self::deposit_event(RawEvent::KeyChanged);
		}

		/// Set the prime member. Must be a current member.
		#[weight = 50_000_000]
		fn set_prime(origin, who: T::AccountId) {
			T::PrimeOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;
			Self::members().binary_search(&who).ok().ok_or(Error::<T, I>::NotMember)?;
			Prime::<T, I>::put(&who);
			T::MembershipChanged::set_prime(Some(who));
		}

		/// Remove the prime member if it exists.
		#[weight = 50_000_000]
		fn clear_prime(origin) {
			T::PrimeOrigin::try_origin(origin)
				.map(|_| ())
				.or_else(ensure_root)?;
			Prime::<T, I>::kill();
			T::MembershipChanged::set_prime(None);
		}
	}
}

impl<T: Trait<I>, I: Instance> Module<T, I> {
	fn rejig_prime(members: &[T::AccountId]) {
		if let Some(prime) = Prime::<T, I>::get() {
			match members.binary_search(&prime) {
				Ok(_) => T::MembershipChanged::set_prime(Some(prime)),
				Err(_) => Prime::<T, I>::kill(),
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	use std::cell::RefCell;
	use frame_support::{
		assert_ok, assert_noop, impl_outer_origin, parameter_types, weights::Weight,
		ord_parameter_types
	};
	use sp_core::H256;
	// The testing primitives are very useful for avoiding having to work with signatures
	// or public keys. `u64` is used as the `AccountId` and no `Signature`s are required.
	use sp_runtime::{Perbill, traits::{BlakeTwo256, IdentityLookup, BadOrigin}, testing::Header};
	use frame_system::EnsureSignedBy;

	impl_outer_origin! {
		pub enum Origin for Test  where system = frame_system {}
	}

	// For testing the pallet, we construct most of a mock runtime. This means
	// first constructing a configuration type (`Test`) which `impl`s each of the
	// configuration traits of pallets we want to use.
	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	parameter_types! {
		pub const BlockHashCount: u64 = 250;
		pub const MaximumBlockWeight: Weight = 1024;
		pub const MaximumBlockLength: u32 = 2 * 1024;
		pub const AvailableBlockRatio: Perbill = Perbill::one();
	}
	impl frame_system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Call = ();
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type BlockHashCount = BlockHashCount;
		type MaximumBlockWeight = MaximumBlockWeight;
		type DbWeight = ();
		type BlockExecutionWeight = ();
		type ExtrinsicBaseWeight = ();
		type MaximumBlockLength = MaximumBlockLength;
		type AvailableBlockRatio = AvailableBlockRatio;
		type Version = ();
		type ModuleToIndex = ();
		type AccountData = ();
		type OnNewAccount = ();
		type OnKilledAccount = ();
	}
	ord_parameter_types! {
		pub const One: u64 = 1;
		pub const Two: u64 = 2;
		pub const Three: u64 = 3;
		pub const Four: u64 = 4;
		pub const Five: u64 = 5;
	}

	thread_local! {
		static MEMBERS: RefCell<Vec<u64>> = RefCell::new(vec![]);
		static PRIME: RefCell<Option<u64>> = RefCell::new(None);
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
			PRIME.with(|p| *p.borrow_mut() = None);
		}
		fn set_prime(who: Option<u64>) {
			PRIME.with(|p| *p.borrow_mut() = who);
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
		type PrimeOrigin = EnsureSignedBy<Five, u64>;
		type MembershipInitialized = TestChangeMembers;
		type MembershipChanged = TestChangeMembers;
	}

	type Membership = Module<Test>;

	// This function basically just builds a genesis storage key/value store according to
	// our desired mockup.
	fn new_test_ext() -> sp_io::TestExternalities {
		let mut t = frame_system::GenesisConfig::default().build_storage::<Test>().unwrap();
		// We use default for brevity, but you can configure as desired if needed.
		GenesisConfig::<Test>{
			members: vec![10, 20, 30],
			.. Default::default()
		}.assimilate_storage(&mut t).unwrap();
		t.into()
	}

	#[test]
	fn query_membership_works() {
		new_test_ext().execute_with(|| {
			assert_eq!(Membership::members(), vec![10, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), vec![10, 20, 30]);
		});
	}

	#[test]
	fn prime_member_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(Membership::set_prime(Origin::signed(4), 20), BadOrigin);
			assert_noop!(Membership::set_prime(Origin::signed(5), 15), Error::<Test, _>::NotMember);
			assert_ok!(Membership::set_prime(Origin::signed(5), 20));
			assert_eq!(Membership::prime(), Some(20));
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());

			assert_ok!(Membership::clear_prime(Origin::signed(5)));
			assert_eq!(Membership::prime(), None);
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());
		});
	}

	#[test]
	fn add_member_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(Membership::add_member(Origin::signed(5), 15), BadOrigin);
			assert_noop!(Membership::add_member(Origin::signed(1), 10), Error::<Test, _>::AlreadyMember);
			assert_ok!(Membership::add_member(Origin::signed(1), 15));
			assert_eq!(Membership::members(), vec![10, 15, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn remove_member_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(Membership::remove_member(Origin::signed(5), 20), BadOrigin);
			assert_noop!(Membership::remove_member(Origin::signed(2), 15), Error::<Test, _>::NotMember);
			assert_ok!(Membership::set_prime(Origin::signed(5), 20));
			assert_ok!(Membership::remove_member(Origin::signed(2), 20));
			assert_eq!(Membership::members(), vec![10, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
			assert_eq!(Membership::prime(), None);
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());
		});
	}

	#[test]
	fn swap_member_works() {
		new_test_ext().execute_with(|| {
			assert_noop!(Membership::swap_member(Origin::signed(5), 10, 25), BadOrigin);
			assert_noop!(Membership::swap_member(Origin::signed(3), 15, 25), Error::<Test, _>::NotMember);
			assert_noop!(Membership::swap_member(Origin::signed(3), 10, 30), Error::<Test, _>::AlreadyMember);

			assert_ok!(Membership::set_prime(Origin::signed(5), 20));
			assert_ok!(Membership::swap_member(Origin::signed(3), 20, 20));
			assert_eq!(Membership::members(), vec![10, 20, 30]);
			assert_eq!(Membership::prime(), Some(20));
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());

			assert_ok!(Membership::set_prime(Origin::signed(5), 10));
			assert_ok!(Membership::swap_member(Origin::signed(3), 10, 25));
			assert_eq!(Membership::members(), vec![20, 25, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
			assert_eq!(Membership::prime(), None);
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());
		});
	}

	#[test]
	fn swap_member_works_that_does_not_change_order() {
		new_test_ext().execute_with(|| {
			assert_ok!(Membership::swap_member(Origin::signed(3), 10, 5));
			assert_eq!(Membership::members(), vec![5, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn change_key_works() {
		new_test_ext().execute_with(|| {
			assert_ok!(Membership::set_prime(Origin::signed(5), 10));
			assert_noop!(Membership::change_key(Origin::signed(3), 25), Error::<Test, _>::NotMember);
			assert_noop!(Membership::change_key(Origin::signed(10), 20), Error::<Test, _>::AlreadyMember);
			assert_ok!(Membership::change_key(Origin::signed(10), 40));
			assert_eq!(Membership::members(), vec![20, 30, 40]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
			assert_eq!(Membership::prime(), Some(40));
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());
		});
	}

	#[test]
	fn change_key_works_that_does_not_change_order() {
		new_test_ext().execute_with(|| {
			assert_ok!(Membership::change_key(Origin::signed(10), 5));
			assert_eq!(Membership::members(), vec![5, 20, 30]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
		});
	}

	#[test]
	fn reset_members_works() {
		new_test_ext().execute_with(|| {
			assert_ok!(Membership::set_prime(Origin::signed(5), 20));
			assert_noop!(Membership::reset_members(Origin::signed(1), vec![20, 40, 30]), BadOrigin);

			assert_ok!(Membership::reset_members(Origin::signed(4), vec![20, 40, 30]));
			assert_eq!(Membership::members(), vec![20, 30, 40]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
			assert_eq!(Membership::prime(), Some(20));
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());

			assert_ok!(Membership::reset_members(Origin::signed(4), vec![10, 40, 30]));
			assert_eq!(Membership::members(), vec![10, 30, 40]);
			assert_eq!(MEMBERS.with(|m| m.borrow().clone()), Membership::members());
			assert_eq!(Membership::prime(), None);
			assert_eq!(PRIME.with(|m| *m.borrow()), Membership::prime());
		});
	}
}
