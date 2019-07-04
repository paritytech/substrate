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
//! next session. It is stored in `NextKeyFor`, a mapping between the caller's `AccountId` and the session
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

use rstd::{prelude::*, marker::PhantomData, ops::{Sub, Rem}};
#[cfg(not(feature = "std"))]
use rstd::alloc::borrow::ToOwned;
#[cfg(feature = "std")]
use runtime_io::with_storage;
use parity_codec::Decode;
use primitives::traits::{Zero, Member, OpaqueKeys};
use srml_support::{
	ConsensusEngineId, StorageValue, StorageMap, for_each_tuple, decl_module,
	decl_event, decl_storage,
};
use srml_support::{ensure, traits::{OnFreeBalanceZero, Get, FindAuthor}, Parameter, print};
use system::ensure_signed;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

pub trait ShouldEndSession<BlockNumber> {
	fn should_end_session(now: BlockNumber) -> bool;
}

/// Ends the session after a fixed period of blocks.
///
/// The first session will have length of `Offset`, and
/// the following sessions will have length of `Period`.
/// This may prove nonsensical if `Offset` >= `Period`.
pub struct PeriodicSessions<
	Period,
	Offset,
>(PhantomData<(Period, Offset)>);

impl<
	BlockNumber: Rem<Output=BlockNumber> + Sub<Output=BlockNumber> + Zero + PartialOrd,
	Period: Get<BlockNumber>,
	Offset: Get<BlockNumber>,
> ShouldEndSession<BlockNumber> for PeriodicSessions<Period, Offset> {
	fn should_end_session(now: BlockNumber) -> bool {
		let offset = Offset::get();
		now >= offset && ((now - offset) % Period::get()).is_zero()
	}
}

pub trait OnSessionEnding<AccountId> {
	/// Handle the fact that the session is ending, and optionally provide the new validator set.
	fn on_session_ending(i: SessionIndex) -> Option<Vec<AccountId>>;
}

impl<A> OnSessionEnding<A> for () {
	fn on_session_ending(_: SessionIndex) -> Option<Vec<A>> { None }
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

/// Handler for selecting the genesis validator set.
pub trait SelectInitialValidators<T: Trait> {
	/// Returns the initial validator set. If `None` is returned
	/// all accounts that have session keys set in the genesis block
	/// will be validators.
	fn select_initial_validators() -> Option<Vec<T::AccountId>>;
}

/// Implementation of `SelectInitialValidators` that does nothing.
pub struct AllValidators;
impl<T: Trait> SelectInitialValidators<T> for AllValidators {
	fn select_initial_validators() -> Option<Vec<T::AccountId>> {
		None
	}
}

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

	/// Select initial validators.
	type SelectInitialValidators: SelectInitialValidators<Self>;
}

type OpaqueKey = Vec<u8>;

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// The current set of validators.
		Validators get(validators): Vec<T::AccountId>;

		/// Current index of the session.
		CurrentIndex get(current_index): SessionIndex;

		/// True if anything has changed in this session.
		Changed: bool;

		/// The next key to be used for a given validator. At the end of the session, they
		/// will be moved into the `QueuedKeys` and so changes here will not take effect for
		/// at least one whole session.
		NextKeyFor get(next_key_for): map T::AccountId => Option<T::Keys>;

		/// Queued keys changed.
		QueuedChanged: bool;

		/// The queued keys for the next session. When the next session begins, these keys
		/// will be used to determine the validator's session keys.
		QueuedKeys get(queued_keys): Vec<(T::AccountId, T::Keys)>;

		/// The keys that are currently active.
		Active: map u32 => Vec<OpaqueKey>;
	}
	add_extra_genesis {
		config(keys): Vec<(T::AccountId, T::Keys)>;
		build(|storage, _, config: &GenesisConfig<T>| {
			with_storage(storage, || {
				let all_validators = config.keys.iter()
					.map(|(validator, _)| validator.to_owned())
					.collect::<Vec<_>>();
				let all_keys = (0..T::Keys::count()).map(|i| (
					i as u32,
					config.keys.iter()
						.map(|x| x.1.get_raw(i).to_vec())
						.collect::<Vec<OpaqueKey>>(),
				)).collect::<Vec<(u32, Vec<OpaqueKey>)>>();
				<Validators<T>>::put(all_validators.clone());
				for (v, sk) in config.keys.clone() {
					<NextKeyFor<T>>::insert(v, sk);
				}
				for (i, keys) in all_keys {
					Active::insert(i, keys);
				}

				let selected_validators =
					T::SelectInitialValidators::select_initial_validators()
					.unwrap_or(all_validators);
				let selected_keys = selected_validators.iter().map(|validator| {
					(
						validator.to_owned(),
						<NextKeyFor<T>>::get(validator)
							.unwrap_or_default()
					)
				}).collect::<Vec<_>>();
				<Validators<T>>::put(selected_validators);
				<QueuedKeys<T>>::put(selected_keys);
			})
		})
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

		/// Sets the session key(s) of the function caller to `key`.
		/// Allows an account to set its session key prior to becoming a validator.
		/// This doesn't take effect until the next session.
		///
		/// The dispatch origin of this function must be signed.
		///
		/// # <weight>
		/// - O(1).
		/// - One extra DB entry.
		/// # </weight>
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
				let mut active = Active::get(i as u32);
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
							print("ERROR: active doesn't contain outgoing key");
						}
					}
				}
				updates.push(Some((i, active)));
			}

			// Update the active sets.
			for (i, active) in updates.into_iter().filter_map(|x| x) {
				Active::insert(i as u32, active);
			}
			// Set new keys value for next session.
			<NextKeyFor<T>>::insert(who, keys);
			// Something changed.
			Changed::put(true);
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
	/// Move on to next session. Register new validator set and session keys. Changes
	/// to the validator set have a session of delay to take effect. This allows for
	/// equivocation punishment after a fork.
	pub fn rotate_session() {
		let session_index = CurrentIndex::get();

		let changed = QueuedChanged::get();
		let mut next_changed = Changed::take();

		// Get queued session keys and validators.
		let session_keys = <QueuedKeys<T>>::get();
		let validators = session_keys.iter()
			.map(|(validator, _)| validator.to_owned())
			.collect::<Vec<_>>();
		<Validators<T>>::put(validators);

		// Get next validator set.
		let maybe_validators = T::OnSessionEnding::on_session_ending(session_index);
		let next_validators = if let Some(validators) = maybe_validators {
			next_changed = true;
			validators
		} else {
			<Validators<T>>::get()
		};

		// Increment session index.
		let session_index = session_index + 1;
		CurrentIndex::put(session_index);

		// Queue next session keys.
		let next_session_keys = next_validators.into_iter()
			.map(|a| { let k = <NextKeyFor<T>>::get(&a).unwrap_or_default(); (a, k) })
			.collect::<Vec<_>>();
		<QueuedKeys<T>>::put(next_session_keys);
		QueuedChanged::put(next_changed);

		// Record that this happened.
		Self::deposit_event(Event::NewSession(session_index));

		// Tell everyone about the new session keys.
		T::SessionHandler::on_new_session::<T::Keys>(changed, &session_keys);
	}

	/// Disable the validator of index `i`.
	pub fn disable_index(i: usize) {
		T::SessionHandler::on_disabled(i);
		Changed::put(true);
	}

	/// Disable the validator identified by `c`. (If using with the staking module, this would be
	/// their *controller* account.)
	pub fn disable(c: &T::AccountId) -> rstd::result::Result<(), ()> {
		Self::validators().iter().position(|i| i == c).map(Self::disable_index).ok_or(())
	}
}

impl<T: Trait> OnFreeBalanceZero<T::AccountId> for Module<T> {
	fn on_free_balance_zero(who: &T::AccountId) {
		<NextKeyFor<T>>::remove(who);
	}
}

/// Wraps the author-scraping logic for consensus engines that can recover
/// the canonical index of an author. This then transforms it into the
/// registering account-ID of that session key index.
pub struct FindAccountFromAuthorIndex<T, Inner>(rstd::marker::PhantomData<(T, Inner)>);

impl<T: Trait, Inner: FindAuthor<u32>> FindAuthor<T::AccountId>
	for FindAccountFromAuthorIndex<T, Inner>
{
	fn find_author<'a, I>(digests: I) -> Option<T::AccountId>
		where I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		let i = Inner::find_author(digests)?;

		let validators = <Module<T>>::validators();
		validators.get(i as usize).map(|k| k.clone())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use std::cell::RefCell;
	use srml_support::{impl_outer_origin, assert_ok};
	use runtime_io::with_externalities;
	use substrate_primitives::{H256, Blake2Hasher};
	use primitives::{
		traits::{BlakeTwo256, IdentityLookup, OnInitialize}, testing::{Header, UintAuthorityId}
	};

	impl_outer_origin!{
		pub enum Origin for Test {}
	}

	thread_local!{
		static NEXT_VALIDATORS: RefCell<Vec<u64>> = RefCell::new(vec![1, 2, 3]);
		static AUTHORITIES: RefCell<Vec<UintAuthorityId>> =
			RefCell::new(vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
		static FORCE_SESSION_END: RefCell<bool> = RefCell::new(false);
		static SESSION_LENGTH: RefCell<u64> = RefCell::new(2);
		static SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
		static TEST_SESSION_CHANGED: RefCell<bool> = RefCell::new(false);
	}

	pub struct TestShouldEndSession;
	impl ShouldEndSession<u64> for TestShouldEndSession {
		fn should_end_session(now: u64) -> bool {
			let l = SESSION_LENGTH.with(|l| *l.borrow());
			now % l == 0 || FORCE_SESSION_END.with(|l| { let r = *l.borrow(); *l.borrow_mut() = false; r })
		}
	}

	pub struct TestSessionHandler;
	impl SessionHandler<u64> for TestSessionHandler {
		fn on_new_session<T: OpaqueKeys>(changed: bool, validators: &[(u64, T)]) {
			SESSION_CHANGED.with(|l| *l.borrow_mut() = changed);
			AUTHORITIES.with(|l|
				*l.borrow_mut() = validators.iter().map(|(_, id)| id.get::<UintAuthorityId>(0).unwrap_or_default()).collect()
			);
		}
		fn on_disabled(_validator_index: usize) {}
	}

	pub struct TestOnSessionEnding;
	impl OnSessionEnding<u64> for TestOnSessionEnding {
		fn on_session_ending(_: SessionIndex) -> Option<Vec<u64>> {
			if !TEST_SESSION_CHANGED.with(|l| *l.borrow()) {
				Some(NEXT_VALIDATORS.with(|l| l.borrow().clone()))
			} else {
				None
			}
		}
	}

	fn authorities() -> Vec<UintAuthorityId> {
		AUTHORITIES.with(|l| l.borrow().to_vec())
	}

	fn force_new_session() {
		FORCE_SESSION_END.with(|l| *l.borrow_mut() = true )
	}

	fn set_session_length(x: u64) {
		SESSION_LENGTH.with(|l| *l.borrow_mut() = x )
	}

	fn session_changed() -> bool {
		SESSION_CHANGED.with(|l| *l.borrow())
	}

	#[derive(Clone, Eq, PartialEq)]
	pub struct Test;
	impl system::Trait for Test {
		type Origin = Origin;
		type Index = u64;
		type BlockNumber = u64;
		type Hash = H256;
		type Hashing = BlakeTwo256;
		type AccountId = u64;
		type Lookup = IdentityLookup<Self::AccountId>;
		type Header = Header;
		type Event = ();
	}
	impl timestamp::Trait for Test {
		type Moment = u64;
		type OnTimestampSet = ();
	}
	impl Trait for Test {
		type ShouldEndSession = TestShouldEndSession;
		type OnSessionEnding = TestOnSessionEnding;
		type SessionHandler = TestSessionHandler;
		type Keys = UintAuthorityId;
		type Event = ();
		type SelectInitialValidators = AllValidators;
	}

	type System = system::Module<Test>;
	type Session = Module<Test>;

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		TEST_SESSION_CHANGED.with(|l| *l.borrow_mut() = false);
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap().0;
		t.extend(timestamp::GenesisConfig::<Test> {
			minimum_period: 5,
		}.build_storage().unwrap().0);
		t.extend(GenesisConfig::<Test> {
			keys: NEXT_VALIDATORS.with(|l|
				l.borrow().iter().cloned().map(|i| (i, UintAuthorityId(i))).collect()
			),
		}.build_storage().unwrap().0);
		runtime_io::TestExternalities::new(t)
	}

	fn initialize_block(block: u64) {
		SESSION_CHANGED.with(|l| *l.borrow_mut() = false);
		System::set_block_number(block);
		Session::on_initialize(block);
	}

	#[test]
	fn simple_setup_should_work() {
		with_externalities(&mut new_test_ext(), || {
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);
			assert_eq!(Session::validators(), vec![1, 2, 3]);
		});
	}

	#[test]
	fn authorities_should_track_validators() {
		with_externalities(&mut new_test_ext(), || {
			NEXT_VALIDATORS.with(|v| *v.borrow_mut() = vec![1, 2]);

			force_new_session();
			initialize_block(1);
			assert_eq!(Session::queued_keys(), vec![
				(1, UintAuthorityId(1)),
				(2, UintAuthorityId(2)),
			]);
			assert_eq!(Session::validators(), vec![1, 2, 3]);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			force_new_session();
			initialize_block(2);
			assert_eq!(Session::queued_keys(), vec![
				(1, UintAuthorityId(1)),
				(2, UintAuthorityId(2)),
			]);
			assert_eq!(Session::validators(), vec![1, 2]);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);

			NEXT_VALIDATORS.with(|v| *v.borrow_mut() = vec![1, 2, 4]);
			assert_ok!(Session::set_keys(Origin::signed(4), UintAuthorityId(4), vec![]));
			force_new_session();
			initialize_block(3);
			assert_eq!(Session::queued_keys(), vec![
				(1, UintAuthorityId(1)),
				(2, UintAuthorityId(2)),
				(4, UintAuthorityId(4)),
			]);
			assert_eq!(Session::validators(), vec![1, 2]);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2)]);

			force_new_session();
			initialize_block(4);
			assert_eq!(Session::queued_keys(), vec![
				(1, UintAuthorityId(1)),
				(2, UintAuthorityId(2)),
				(4, UintAuthorityId(4)),
			]);
			assert_eq!(Session::validators(), vec![1, 2, 4]);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(4)]);
		});
	}

	#[test]
	fn should_work_with_early_exit() {
		with_externalities(&mut new_test_ext(), || {
			set_session_length(10);

			initialize_block(1);
			assert_eq!(Session::current_index(), 0);

			initialize_block(2);
			assert_eq!(Session::current_index(), 0);

			force_new_session();
			initialize_block(3);
			assert_eq!(Session::current_index(), 1);

			initialize_block(9);
			assert_eq!(Session::current_index(), 1);

			initialize_block(10);
			assert_eq!(Session::current_index(), 2);
		});
	}

	#[test]
	fn session_change_should_work() {
		with_externalities(&mut new_test_ext(), || {
			// Block 1: No change
			initialize_block(1);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 2: Session rollover, but no change.
			initialize_block(2);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 3: Set new key for validator 2; no visible change.
			initialize_block(3);
			assert_ok!(Session::set_keys(Origin::signed(2), UintAuthorityId(5), vec![]));
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 4: Session rollover; no visible change.
			initialize_block(4);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 5: No change.
			initialize_block(5);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(2), UintAuthorityId(3)]);

			// Block 6: Session rollover; authority 2 changes.
			initialize_block(6);
			assert_eq!(authorities(), vec![UintAuthorityId(1), UintAuthorityId(5), UintAuthorityId(3)]);
		});
	}

	#[test]
	fn session_changed_flag_works() {
		with_externalities(&mut new_test_ext(), || {
			TEST_SESSION_CHANGED.with(|l| *l.borrow_mut() = true);

			force_new_session();
			initialize_block(1);
			assert!(!session_changed());

			force_new_session();
			initialize_block(2);
			assert!(!session_changed());

			Session::disable_index(0);
			force_new_session();
			initialize_block(3);
			assert!(!session_changed());

			force_new_session();
			initialize_block(4);
			assert!(session_changed());

			force_new_session();
			initialize_block(5);
			assert!(!session_changed());

			assert_ok!(Session::set_keys(Origin::signed(2), UintAuthorityId(5), vec![]));
			force_new_session();
			initialize_block(6);
			assert!(!session_changed());

			force_new_session();
			initialize_block(7);
			assert!(session_changed());
		});
	}

	#[test]
	fn periodic_session_works() {
		struct Period;
		struct Offset;

		impl Get<u64> for Period {
			fn get() -> u64 { 10 }
		}

		impl Get<u64> for Offset {
			fn get() -> u64 { 3 }
		}


		type P = PeriodicSessions<Period, Offset>;

		for i in 0..3 {
			assert!(!P::should_end_session(i));
		}

		assert!(P::should_end_session(3));

		for i in (1..10).map(|i| 3 + i) {
			assert!(!P::should_end_session(i));
		}

		assert!(P::should_end_session(13));
	}
}
