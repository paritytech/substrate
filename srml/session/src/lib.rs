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

//! # Session Module
//!
//! The Session module allows validators to manage their session keys, provides a function for changing
//! the session length, and handles session rotation.
//!
//! - [`session::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Overview
//!
//! ### Terminology
//! <!-- Original author of paragraph: @gavofyork -->
//!
//! - **Session:** A session is a period of time that has a constant set of validators. Validators can only join
//! or exit the validator set at a session change. It is measured in block numbers and set with `set_length`
//! during a session for use in subsequent sessions.
//! - **Session key:** A session key is actually several keys kept together that provide the various signing
//! functions required by network authorities/validators in pursuit of their duties.
//! - **Session key configuration process:** A session key is set using `set_key` for use in the
//! next session. It is stored in `NextKeyFor`, a mapping between the caller's `AccountID` and the session
//! key provided. `set_key` allows users to set their session key prior to becoming a validator.
//! It is a public call since it uses `ensure_signed`, which checks that the origin is a signed account.
//! As such, the account ID of the origin stored in in `NextKeyFor` may not necessarily be associated with
//! a block author or a validator. The session keys of accounts are removed once their account balance is zero.
//! - **Validator set session key configuration process:** Each session we iterate through the current
//! set of validator account IDs to check if a session key was created for it in the previous session
//! using `set_key`. If it was then we call `set_authority` from the [Consensus module](../srml_consensus/index.html)
//! and pass it a set of session keys (each associated with an account ID) as the session keys for the new
//! validator set. Lastly, if the session key of the current authority does not match any session keys stored under
//! its validator index in the `AuthorityStorageVec` mapping, then we update the mapping with its session
//! key and update the saved list of original authorities if necessary
//! (see https://github.com/paritytech/substrate/issues/1290). Note: Authorities are stored in the Consensus module.
//! They are represented by a validator account ID index from the Session module and allocated with a session
//! key for the length of the session.
//! - **Session length change process:** At the start of the next session we allocate a session index and record the
//! timestamp when the session started. If a `NextSessionLength` was recorded in the previous session, we record
//! it as the new session length. Additionally, if the new session length differs from the length of the
//! next session then we record a `LastLengthChange`.
//! - **Session rotation configuration:** Configure as either a 'normal' (rewardable session where rewards are
//! applied) or 'exceptional' (slashable) session rotation.
//! - **Session rotation process:** The session is changed at the end of the final block of the current session
//! using the `on_finalize` method. It may be called by either an origin or internally from another runtime
//! module at the end of each block.
//!
//! ### Goals
//!
//! The Session module in Substrate is designed to make the following possible:
//!
//! - Set session keys of the validator set for the next session.
//! - Set the length of a session.
//! - Configure and switch between either normal or exceptional session rotations.
//!
//! ## Interface
//!
//! ### Dispatchable Functions
//!
//! - `set_key` - Set a validator's session key for the next session.
//! - `set_length` - Set a new session length to be applied upon the next session change.
//! - `force_new_session` - Force a new session that should be considered either a normal (rewardable)
//! or exceptional rotation.
//! - `on_finalize` - Called when a block is finalized. Will rotate session if it is the last
//! block of the current session.
//!
//! ### Public Functions
//!
//! - `validator_count` - Get the current number of validators.
//! - `last_length_change` - Get the block number when the session length last changed.
//! - `apply_force_new_session` - Force a new session. Can be called by other runtime modules.
//! - `set_validators` - Set the current set of validators. Can only be called by the Staking module.
//! - `check_rotate_session` - Rotate the session and apply rewards if necessary. Called after the Staking
//! module updates the authorities to the new validator set.
//! - `rotate_session` - Change to the next session. Register the new authority set. Update session keys.
//! Enact session length change if applicable.
//! - `ideal_session_duration` - Get the time of an ideal session.
//! - `blocks_remaining` - Get the number of blocks remaining in the current session,
//! excluding the current block.
//!
//! ## Usage
//!
//! ### Example from the SRML
//!
//! The [Staking module](../srml_staking/index.html) uses the Session module to get the validator set.
//!
//! ```
//! use srml_session as session;
//! # fn not_executed<T: session::Trait>() {
//!
//! let validators = <session::Module<T>>::validators();
//! # }
//! # fn main(){}
//! ```
//!
//! ## Related Modules
//!
//! - [Consensus](../srml_consensus/index.html)
//! - [Staking](../srml_staking/index.html)
//! - [Timestamp](../srml_timestamp/index.html)

#![cfg_attr(not(feature = "std"), no_std)]

use rstd::{prelude::*, marker::PhantomData, ops::Rem};
use parity_codec::Decode;
use primitives::traits::{Zero, Saturating, Member};
use srml_support::{StorageValue, StorageMap, for_each_tuple, decl_module, decl_event, decl_storage};
use srml_support::{ensure, traits::{OnFreeBalanceZero, Get}, Parameter};
use system::ensure_signed;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

/// Opaque datatype that may be destructured into a series of raw byte slices (which represent
/// individual keys).
pub trait OpaqueKeys {
	fn count() -> usize { 0 }
	fn get_raw(&self, i: usize) -> &[u8];
	fn get<T: Decode>(&self, i: usize) -> Option<T> { T::decode(&mut self.get_raw(i)) }
	fn ownership_proof_is_valid(&self, _proof: &[u8]) -> bool { true }
}

/// Calls a given macro a number of times with a set of fixed params and an incrementing numeral.
/// e.g.
/// ```
/// count!(println ("{}",) foo, bar, baz);
/// // Will result in three `println!`s: "0", "1" and "2".
/// ```
#[macro_export]
macro_rules! count {
	($f:ident ($($x:tt)*) ) => ();
	($f:ident ($($x:tt)*) $x1:tt) => { $f!($($x)* 0); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt) => { $f!($($x)* 0); $f!($($x)* 1); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt) => { $f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); };
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt, $x4:tt) => {
		$f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); $f!($($x)* 3);
	};
	($f:ident ($($x:tt)*) $x1:tt, $x2:tt, $x3:tt, $x4:tt, $x5:tt) => {
		$f!($($x)* 0); $f!($($x)* 1); $f!($($x)* 2); $f!($($x)* 3); $f!($($x)* 4);
	};
}

#[macro_export]
/// Just implement `OpaqueKeys` for a given tuple-struct.
/// Would be much nicer for this to be converted to `derive` code.
macro_rules! impl_opaque_keys {
	(
		pub struct $name:ident ( $( $t:tt ,)* );
	) => {
		impl_opaque_keys! {
			pub struct $name ( $( $t ,)* );
			impl OpaqueKeys for _ {}
		}
	};
	(
		pub struct $name:ident ( $( $t:tt ,)* );
		impl OpaqueKeys for _ {
			$($rest:tt)*
		}
	) => {
		#[derive(Default, Clone, PartialEq, Eq, Encode, Decode)]
		#[cfg_attr(feature = "std", derive(Debug, Serialize, Deserialize))]
		pub struct $name($( pub $t ,)*);
		impl $crate::OpaqueKeys for $name {
			fn count() -> usize {
				let mut c = 0;
				$( let _: $t; c += 1; )*
				c
			}
			fn get_raw(&self, i: usize) -> &[u8] {
				$crate::count!(impl_opaque_keys (!! self i) $($t),*);
				&[]
			}
			$($rest)*
		}
	};
	( !! $self:ident $param_i:ident $i:tt) => {
		if $param_i == $i { return $self.$i.as_ref() }
	}
}

pub trait ShouldEndSession<BlockNumber> {
	fn should_end_session(now: BlockNumber) -> bool;
}

pub struct PeriodicSessions<
	Period,
	Offset,
>(PhantomData<(Period, Offset)>);

impl<
	BlockNumber: Rem<Output=BlockNumber> + Saturating + Zero,
	Period: Get<BlockNumber>,
	Offset: Get<BlockNumber>,
> ShouldEndSession<BlockNumber> for PeriodicSessions<Period, Offset> {
	fn should_end_session(now: BlockNumber) -> bool {
		((now.saturating_sub(Offset::get())) % Period::get()).is_zero()
	}
}

pub trait OnSessionEnding<AccountId> {
	/// Handle the fact that the session is ending, and optionally provide the new validator set.
	fn on_session_ending(i: SessionIndex) -> Option<Vec<AccountId>>;
}

/// Handler for when a session keys set changes.
pub trait SessionHandler<AccountId> {
	/// Session set has changed; act appropriately.
	fn on_new_session<Ks: OpaqueKeys>(changed: bool, validators: &[(AccountId, Ks)]);

	/// A validator got disabled. Act accordingly until a new session begins.
	fn on_disabled(validator_index: usize);
}

pub trait OneSessionHandler<AccountId> {
	type Key: Decode + Default;
	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a AccountId, Self::Key)>, AccountId: 'a;
	fn on_disabled(i: usize);
}

macro_rules! impl_session_handlers {
	() => (
		impl<AId> SessionHandler<AId> for () {
			fn on_new_session<Ks: OpaqueKeys>(_: bool, _: &[(AId, Ks)]) {}
			fn on_disabled(_: usize) {}
		}
	);

	( $($t:ident)* ) => {
		impl<AId, $( $t: OneSessionHandler<AId> ),*> SessionHandler<AId> for ( $( $t , )* ) {
			fn on_new_session<Ks: OpaqueKeys>(changed: bool, validators: &[(AId, Ks)]) {
				let mut i: usize = 0;
				$(
					i += 1;
					let our_keys = validators.iter()
						.map(|k| (&k.0, k.1.get::<$t::Key>(i - 1).unwrap_or_default()));
					$t::on_new_session(changed, our_keys);
				)*
			}
			fn on_disabled(i: usize) {
				$(
					$t::on_disabled(i);
				)*
			}
		}
	}
}

for_each_tuple!(impl_session_handlers);


pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;

	/// Indicator for when to end the session.
	type ShouldEndSession: ShouldEndSession<Self::BlockNumber>;

	/// Handler for when a session is about to end.
	type OnSessionEnding: OnSessionEnding<Self::AccountId>;

	/// Handler when a session has changed.
	type SessionHandler: SessionHandler<Self::AccountId>;

	/// The keys.
	type Keys: OpaqueKeys + Member + Parameter + Default;
}

type OpaqueKey = Vec<u8>;

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// The current set of validators.
		pub Validators get(validators) config(): Vec<T::AccountId>;

		/// Current index of the session.
		pub CurrentIndex get(current_index): SessionIndex;

		/// True if anything has changed in this session.
		Changed: bool;

		/// The next key for a given validator.
		NextKeyFor build(|config: &GenesisConfig<T>| {
			config.keys.clone()
		}): map T::AccountId => Option<T::Keys>;

		/// The keys that are currently active.
		Active build(|config: &GenesisConfig<T>| {
			(0..T::Keys::count()).map(|i| (
				i as u32,
				config.keys.iter()
					.map(|x| x.1.get_raw(i).to_vec())
					.collect::<Vec<OpaqueKey>>(),
			)).collect::<Vec<(u32, Vec<OpaqueKey>)>>()
		}): map u32 => Vec<OpaqueKey>;
	}
	add_extra_genesis {
		config(keys): Vec<(T::AccountId, T::Keys)>;
	}
}

decl_event!(
	pub enum Event {
		/// New session has happened. Note that the argument is the session index, not the block
		/// number as the type might suggest.
		NewSession(SessionIndex),
	}
);

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Sets the session key of a validator (function caller) to `key`.
		/// This doesn't take effect until the next session.
		fn set_keys(origin, keys: T::Keys, proof: Vec<u8>) {
			let who = ensure_signed(origin)?;

			ensure!(keys.ownership_proof_is_valid(&proof), "invalid ownership proof");

			let old_keys = <NextKeyFor<T>>::get(&who);
			let mut updates = vec![];

			for i in 0..T::Keys::count() {
				let new_key = keys.get_raw(i);
				let maybe_old_key = old_keys.as_ref().map(|o| o.get_raw(i));
				if maybe_old_key == Some(new_key) {
					// no change.
					updates.push(None);
					continue;
				}
				let mut active = <Active<T>>::get(i as u32);
				match active.binary_search_by(|k| k[..].cmp(&new_key)) {
					Ok(_) => return Err("duplicate key provided"),
					Err(pos) => active.insert(pos, new_key.to_owned()),
				}
				if let Some(old_key) = maybe_old_key {
					match active.binary_search_by(|k| k[..].cmp(&old_key)) {
						Ok(pos) => { active.remove(pos); }
						Err(_) => {
							// unreachable as long as our state is valid. we don't want to panic if
							// it isn't, though.
						}
					}
				}
				updates.push(Some((i, active)));
			}

			// Update the active sets.
			for (i, active) in updates.into_iter().filter_map(|x| x) {
				<Active<T>>::insert(i as u32, active);
			}
			// Set new keys value for next session.
			<NextKeyFor<T>>::insert(who, keys);
			// Something changed.
			<Changed<T>>::put(true);
		}

		/// Called when a block is finalized. Will rotate session if it is the last
		/// block of the current session.
		fn on_initialize(n: T::BlockNumber) {
			if T::ShouldEndSession::should_end_session(n) {
				Self::rotate_session();
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Move on to next session: register the new authority set.
	pub fn rotate_session() {
		// Increment current session index.
		let session_index = <CurrentIndex<T>>::get();

		let mut changed = <Changed<T>>::take();

		// See if we have a new validator set.
		let validators = if let Some(new) = T::OnSessionEnding::on_session_ending(session_index) {
			changed = true;
			<Validators<T>>::put(&new);
			new
		} else {
			<Validators<T>>::get()
		};

		let session_index = session_index + 1;
		<CurrentIndex<T>>::put(session_index);

		// Record that this happened.
		Self::deposit_event(Event::NewSession(session_index));

		// Tell everyone about the new session keys.
		let amalgamated = validators.into_iter()
			.map(|a| { let k = <NextKeyFor<T>>::get(&a).unwrap_or_default(); (a, k) })
			.collect::<Vec<_>>();
		T::SessionHandler::on_new_session::<T::Keys>(changed, &amalgamated);
	}

	/// Disable the validator of index `i`.
	pub fn disable(i: usize) {
		T::SessionHandler::on_disabled(i);
		<Changed<T>>::put(true);
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		<NextKeyFor<T>>::remove(who);
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::cell::RefCell;
	use srml_support::{impl_outer_origin, assert_ok};
	use runtime_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	use primitives::BuildStorage;
	use primitives::traits::{BlakeTwo256, IdentityLookup};
	use primitives::testing::{Digest, DigestItem, Header, UintAuthorityId, ConvertUintAuthorityId};

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	thread_local!{
		static NEXT_VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
	}

	pub struct TestOnNewSession;
	impl OnNewSession<u64> for TestOnNewSession {
		fn on_new_session(_elapsed: u64, _should_reward: bool) {
			NEXT_VALIDATORS.with(|v| Session::set_validators(&*v.borrow()));
		}
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl consensus::Trait for Test {
		type Log = DigestItem;
		type SessionKey = UintAuthorityId;
		type InherentOfflineReport = ();
	}
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type Digest = Digest;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
		type Log = DigestItem;
	}
	impl timestamp::Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
	}
	impl Trait for Test {
		type ConvertAccountIdToSessionKey = ConvertUintAuthorityId;
		type OnNewSession = TestOnNewSession;
		type Event = ();
	}

	type System = system::Module<Test>;
	type Consensus = consensus::Module<Test>;
	type Session = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::<Test>::default().build_storage().unwrap().0;
		t.extend(consensus::GenesisConfig::<Test>{
			code: vec![],
			authorities: NEXT_VALIDATORS.with(|l| l.borrow().iter().cloned().map(UintAuthorityId).collect()),
		}.build_storage().unwrap().0);
		t.extend(timestamp::GenesisConfig::<Test>{
			minimum_period: 5,
		}.build_storage().unwrap().0);
		t.extend(GenesisConfig::<Test>{
			session_length: 2,
			validators: NEXT_VALIDATORS.with(|l| l.borrow().clone()),
			keys: vec![],
		}.build_storage().unwrap().0);
		runtime_io::TestExternalities::new(t)
	}

	#[test]
	fn simple_setup_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::validators(), vec![1, 2, 3]);
		});
	}

	#[test]
	fn authorities_should_track_validators() {
		with_externalities(&mut new_test_ext(), || {
			NEXT_VALIDATORS.with(|v| *v.borrow_mut() = vec![1, 2]);
			assert_ok!(Session::force_new_session(false));
			Session::check_rotate_session(1);
			assert_eq!(Session::validators(), vec![1, 2]);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);

			NEXT_VALIDATORS.with(|v| *v.borrow_mut() = vec![1, 2, 4]);
			assert_ok!(Session::force_new_session(false));
			Session::check_rotate_session(2);
			assert_eq!(Session::validators(), vec![1, 2, 4]);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(4)]);

			NEXT_VALIDATORS.with(|v| *v.borrow_mut() = vec![1, 2, 3]);
			assert_ok!(Session::force_new_session(false));
			Session::check_rotate_session(3);
			assert_eq!(Session::validators(), vec![1, 2, 3]);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		});
	}

	#[test]
	fn should_work_with_early_exit() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			assert_ok!(Session::set_length(10));
			assert_eq!(Session::blocks_remaining(), 1);
			Session::check_rotate_session(1);

			System::set_block_number(2);
			assert_eq!(Session::blocks_remaining(), 0);
			Session::check_rotate_session(2);
			assert_eq!(Session::length(), 10);

			System::set_block_number(7);
			assert_eq!(Session::current_index(), 1);
			assert_eq!(Session::blocks_remaining(), 5);
			assert_ok!(Session::force_new_session(false));
			Session::check_rotate_session(7);

			System::set_block_number(8);
			assert_eq!(Session::current_index(), 2);
			assert_eq!(Session::blocks_remaining(), 9);
			Session::check_rotate_session(8);

			System::set_block_number(17);
			assert_eq!(Session::current_index(), 2);
			assert_eq!(Session::blocks_remaining(), 0);
			Session::check_rotate_session(17);

			System::set_block_number(18);
			assert_eq!(Session::current_index(), 3);
		});
	}

	#[test]
	fn session_length_change_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// Block 1: Change to length 3; no visible change.
			System::set_block_number(1);
			assert_ok!(Session::set_length(3));
			Session::check_rotate_session(1);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 0);

			// Block 2: Length now changed to 3. Index incremented.
			System::set_block_number(2);
			assert_ok!(Session::set_length(3));
			Session::check_rotate_session(2);
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 3: Length now changed to 3. Index incremented.
			System::set_block_number(3);
			Session::check_rotate_session(3);
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 4: Change to length 2; no visible change.
			System::set_block_number(4);
			assert_ok!(Session::set_length(2));
			Session::check_rotate_session(4);
			assert_eq!(Session::length(), 3);
			assert_eq!(Session::current_index(), 1);

			// Block 5: Length now changed to 2. Index incremented.
			System::set_block_number(5);
			Session::check_rotate_session(5);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 2);

			// Block 6: No change.
			System::set_block_number(6);
			Session::check_rotate_session(6);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 2);

			// Block 7: Next index.
			System::set_block_number(7);
			Session::check_rotate_session(7);
			assert_eq!(Session::length(), 2);
			assert_eq!(Session::current_index(), 3);
		});
	}

	#[test]
	fn session_change_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// Block 1: No change
			System::set_block_number(1);
			Session::check_rotate_session(1);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 2: Session rollover, but no change.
			System::set_block_number(2);
			Session::check_rotate_session(2);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 3: Set new key for validator 2; no visible change.
			System::set_block_number(3);
			assert_ok!(Session::set_key(Origin::signed(2), UintAuthorityId(5)));
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			Session::check_rotate_session(3);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 4: Session rollover, authority 2 changes.
			System::set_block_number(4);
			Session::check_rotate_session(4);
			assert_eq!(Consensus::authorities(), vec![UintAuthorityId(1), UintAuthorityId(5), UintAuthorityId(3)]);
		});
	}
}
