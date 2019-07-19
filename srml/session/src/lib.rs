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
//! or exit the validator set at a session change. It is measured in block numbers. The block where a session is
//! ended is determined by the `ShouldSessionEnd` trait. When the session is ending, a new validator set
//! can be chosen by `OnSessionEnding` implementations.
//! - **Session key:** A session key is actually several keys kept together that provide the various signing
//! functions required by network authorities/validators in pursuit of their duties.
//! - **Validator ID:** Every account has an associated validator ID. For some simple staking systems, this
//! may just be the same as the account ID. For staking systems using a stash/controller model,
//! the validator ID would be the stash account ID of the controller.
//! - **Session key configuration process:** A session key is set using `set_key` for use in the
//! next session. It is stored in `NextKeyFor`, a mapping between the caller's `ValidatorId` and the session
//! keys provided. `set_key` allows users to set their session key prior to being selected as validator.
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
use parity_codec::{Decode, Encode};
use primitives::KeyTypeId;
use primitives::traits::{Convert, Zero, Member, OpaqueKeys, TypedKey, Hash};
use srml_support::{
	dispatch::Result,
	storage,
	ConsensusEngineId, StorageValue, for_each_tuple, decl_module,
	decl_event, decl_storage,
};
use srml_support::{ensure, traits::{OnFreeBalanceZero, Get, FindAuthor}, Parameter};
use system::{self, ensure_signed};

#[cfg(test)]
mod mock;

#[cfg(feature = "historical")]
pub mod historical;

/// Simple index type with which we can count sessions.
pub type SessionIndex = u32;

/// Decides whether the session should be ended.
pub trait ShouldEndSession<BlockNumber> {
	/// Return `true` if the session should be ended.
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

/// An event handler for when the session is ending.
pub trait OnSessionEnding<ValidatorId> {
	/// Handle the fact that the session is ending, and optionally provide the new validator set.
	///
	/// `ending_index` is the index of the currently ending session.
	/// The returned validator set, if any, will not be applied until `next_index`.
	/// `next_index` is guaranteed to be at least `ending_index + 1`, since session indices don't
	/// repeat.
	fn on_session_ending(ending_index: SessionIndex, next_index: SessionIndex) -> Option<Vec<ValidatorId>>;
}

impl<A> OnSessionEnding<A> for () {
	fn on_session_ending(_: SessionIndex, _: SessionIndex) -> Option<Vec<A>> { None }
}

/// Handler for when a session keys set changes.
pub trait SessionHandler<ValidatorId> {
	/// Session set has changed; act appropriately.
	fn on_new_session<Ks: OpaqueKeys>(changed: bool, validators: &[(ValidatorId, Ks)]);

	/// A validator got disabled. Act accordingly until a new session begins.
	fn on_disabled(validator_index: usize);
}

/// One session-key type handler.
pub trait OneSessionHandler<ValidatorId> {
	/// The key type expected.
	type Key: Decode + Default + TypedKey;

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a ValidatorId, Self::Key)>, ValidatorId: 'a;
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
				$(
					let our_keys = validators.iter()
						.map(|k| (&k.0, k.1.get::<$t::Key>(<$t::Key as TypedKey>::KEY_TYPE)
							.unwrap_or_default()));
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
pub trait SelectInitialValidators<ValidatorId> {
	/// Returns the initial validator set. If `None` is returned
	/// all accounts that have session keys set in the genesis block
	/// will be validators.
	fn select_initial_validators() -> Option<Vec<ValidatorId>>;
}

/// Implementation of `SelectInitialValidators` that does nothing.
impl<V> SelectInitialValidators<V> for () {
	fn select_initial_validators() -> Option<Vec<V>> {
		None
	}
}

pub trait Trait: system::Trait {
	/// The overarching event type.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;

	/// A stable ID for a validator.
	type ValidatorId: Member + Parameter;

	/// A conversion to validator ID to account ID.
	type ValidatorIdOf: Convert<Self::AccountId, Option<Self::ValidatorId>>;

	/// Indicator for when to end the session.
	type ShouldEndSession: ShouldEndSession<Self::BlockNumber>;

	/// Handler for when a session is about to end.
	type OnSessionEnding: OnSessionEnding<Self::ValidatorId>;

	/// Handler when a session has changed.
	type SessionHandler: SessionHandler<Self::ValidatorId>;

	/// The keys.
	type Keys: OpaqueKeys + Member + Parameter + Default;

	/// Select initial validators.
	type SelectInitialValidators: SelectInitialValidators<Self::ValidatorId>;
}

const DEDUP_KEY_LEN: usize = 13;
const DEDUP_KEY_PREFIX: &[u8; DEDUP_KEY_LEN] = b":session:keys";

decl_storage! {
	trait Store for Module<T: Trait> as Session {
		/// The current set of validators.
		Validators get(validators): Vec<T::ValidatorId>;

		/// Current index of the session.
		CurrentIndex get(current_index): SessionIndex;

		/// True if anything has changed in this session.
		Changed: bool;

		/// Queued keys changed.
		QueuedChanged: bool;

		/// The queued keys for the next session. When the next session begins, these keys
		/// will be used to determine the validator's session keys.
		QueuedKeys get(queued_keys): Vec<(T::ValidatorId, T::Keys)>;

	}
	add_extra_genesis {
		config(keys): Vec<(T::ValidatorId, T::Keys)>;
		build(|
			storage: &mut primitives::StorageOverlay,
			_: &mut primitives::ChildrenStorageOverlay,
			config: &GenesisConfig<T>
		| {
			runtime_io::with_storage(storage, || {
				for (who, keys) in config.keys.iter().cloned() {
					assert!(
						<Module<T>>::load_keys(&who).is_none(),
						"genesis config contained duplicate validator {:?}", who,
					);

					<Module<T>>::do_set_keys(&who, keys)
						.expect("genesis config must not contain duplicates; qed");
				}

				let initial_validators = T::SelectInitialValidators::select_initial_validators()
					.unwrap_or_else(|| config.keys.iter().map(|(ref v, _)| v.clone()).collect());

				assert!(!initial_validators.is_empty(), "Empty validator set in genesis block!");

				let queued_keys: Vec<_> = initial_validators
					.iter()
					.cloned()
					.map(|v| (
						v.clone(),
						<Module<T>>::load_keys(&v).unwrap_or_default(),
					))
					.collect();

				<Validators<T>>::put(initial_validators);
				<QueuedKeys<T>>::put(queued_keys);
			});
		});
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
		/// - O(log n) in number of accounts.
		/// - One extra DB entry.
		/// # </weight>
		fn set_keys(origin, keys: T::Keys, proof: Vec<u8>) -> Result {
			let who = ensure_signed(origin)?;

			ensure!(keys.ownership_proof_is_valid(&proof), "invalid ownership proof");

			let who = match T::ValidatorIdOf::convert(who) {
				Some(val_id) => val_id,
				None => return Err("no associated validator ID for account."),
			};

			Self::do_set_keys(&who, keys)?;

			// Something changed.
			Changed::put(true);

			Ok(())
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
			.map(|(validator, _)| validator.clone())
			.collect::<Vec<_>>();
		<Validators<T>>::put(&validators);

		let applied_at = session_index + 2;

		// Get next validator set.
		let maybe_validators = T::OnSessionEnding::on_session_ending(session_index, applied_at);
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
		let queued_amalgamated = next_validators.into_iter()
			.map(|a| { let k = Self::load_keys(&a).unwrap_or_default(); (a, k) })
			.collect::<Vec<_>>();

		<QueuedKeys<T>>::put(queued_amalgamated);
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
	/// their *stash* account.)
	pub fn disable(c: &T::ValidatorId) -> rstd::result::Result<(), ()> {
		Self::validators().iter().position(|i| i == c).map(Self::disable_index).ok_or(())
	}

	// perform the set_key operation, checking for duplicates.
	// does not set `Changed`.
	fn do_set_keys(who: &T::ValidatorId, keys: T::Keys) -> Result {
		let old_keys = Self::load_keys(&who);

		for id in T::Keys::key_ids() {
			let key = keys.get_raw(id);

			// ensure keys are without duplication.
			ensure!(
				Self::key_owner(id, key).map_or(true, |owner| &owner == who),
				"registered duplicate key"
			);

			if let Some(old) = old_keys.as_ref().map(|k| k.get_raw(id)) {
				if key == old {
					continue;
				}

				Self::clear_key_owner(id, old);
			}

			Self::put_key_owner(id, key, &who);
		}

		Self::put_keys(&who, &keys);

		Ok(())
	}

	fn prune_dead_keys(who: &T::ValidatorId) {
		if let Some(old_keys) = Self::take_keys(who) {
			for id in T::Keys::key_ids() {
				let key_data = old_keys.get_raw(id);
				Self::clear_key_owner(id, key_data);
			}

			Changed::put(true);
		}
	}

	// Child trie storage.

	fn load_keys(v: &T::ValidatorId) -> Option<T::Keys> {
		storage::unhashed::get(&dedup_trie_key::<T, _>(v))
	}

	fn take_keys(v: &T::ValidatorId) -> Option<T::Keys> {
		storage::unhashed::take(&dedup_trie_key::<T, _>(v))
	}

	fn put_keys(v: &T::ValidatorId, keys: &T::Keys) {
		storage::unhashed::put(&dedup_trie_key::<T, _>(v), keys)
	}

	fn key_owner(id: KeyTypeId, key_data: &[u8]) -> Option<T::ValidatorId> {
		storage::unhashed::get(&dedup_trie_key::<T, _>(&(id, key_data)))
	}

	fn put_key_owner(id: KeyTypeId, key_data: &[u8], v: &T::ValidatorId) {
		storage::unhashed::put(&dedup_trie_key::<T, _>(&(id, key_data)), v);
	}

	fn clear_key_owner(id: KeyTypeId, key_data: &[u8]) {
		storage::unhashed::kill(&dedup_trie_key::<T, _>(&(id, key_data)));
	}
}

fn dedup_trie_key<T: Trait, K: Encode>(key: &K) -> [u8; 32 + DEDUP_KEY_LEN] {
	key.using_encoded(|s| {
		// take at most 32 bytes from the hash of the value.
		let hash = <T as system::Trait>::Hashing::hash(s);
		let hash: &[u8] = hash.as_ref();
		let len = rstd::cmp::min(hash.len(), 32);

		let mut data = [0; 32 + DEDUP_KEY_LEN];
		data[..DEDUP_KEY_LEN].copy_from_slice(DEDUP_KEY_PREFIX);
		data[DEDUP_KEY_LEN..][..len].copy_from_slice(hash);
		data
	})
}

impl<T: Trait> OnFreeBalanceZero<T::ValidatorId> for Module<T> {
	fn on_free_balance_zero(who: &T::ValidatorId) {
		Self::prune_dead_keys(who);
	}
}

/// Wraps the author-scraping logic for consensus engines that can recover
/// the canonical index of an author. This then transforms it into the
/// registering account-ID of that session key index.
pub struct FindAccountFromAuthorIndex<T, Inner>(rstd::marker::PhantomData<(T, Inner)>);

impl<T: Trait, Inner: FindAuthor<u32>> FindAuthor<T::ValidatorId>
	for FindAccountFromAuthorIndex<T, Inner>
{
	fn find_author<'a, I>(digests: I) -> Option<T::ValidatorId>
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
	use srml_support::assert_ok;
	use runtime_io::with_externalities;
	use substrate_primitives::Blake2Hasher;
	use primitives::{
		traits::OnInitialize,
		testing::UintAuthorityId,
	};
	use mock::{
		NEXT_VALIDATORS, SESSION_CHANGED, TEST_SESSION_CHANGED, authorities, force_new_session,
		set_next_validators, set_session_length, session_changed, Test, Origin, System, Session,
	};

	fn new_test_ext() -> runtime_io::TestExternalities<Blake2Hasher> {
		let mut t = system::GenesisConfig::default().build_storage::<Test>().unwrap();
		GenesisConfig::<Test> {
			keys: NEXT_VALIDATORS.with(|l|
				l.borrow().iter().cloned().map(|i| (i, UintAuthorityId(i))).collect()
			),
		}.assimilate_storage(&mut t.0, &mut t.1).unwrap();
		runtime_io::TestExternalities::new_with_children(t)
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
	fn put_get_keys() {
		with_externalities(&mut new_test_ext(), || {
			Session::put_keys(&10, &UintAuthorityId(10));
			assert_eq!(Session::load_keys(&10), Some(UintAuthorityId(10)));
		})
	}

	#[test]
	fn keys_cleared_on_kill() {
		let mut ext = new_test_ext();
		with_externalities(&mut ext, || {
			assert_eq!(Session::validators(), vec![1, 2, 3]);
			assert_eq!(Session::load_keys(&1), Some(UintAuthorityId(1)));

			let id = <UintAuthorityId as TypedKey>::KEY_TYPE;
			assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), Some(1));

			Session::on_free_balance_zero(&1);
			assert_eq!(Session::load_keys(&1), None);
			assert_eq!(Session::key_owner(id, UintAuthorityId(1).get_raw(id)), None);

			assert!(Changed::get());
		})
	}

	#[test]
	fn authorities_should_track_validators() {
		with_externalities(&mut new_test_ext(), || {
			set_next_validators(vec![1, 2]);
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

			set_next_validators(vec![1, 2, 4]);
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
	fn duplicates_are_not_allowed() {
		with_externalities(&mut new_test_ext(), || {
			System::set_block_number(1);
			Session::on_initialize(1);
			assert!(Session::set_keys(Origin::signed(4), UintAuthorityId(1), vec![]).is_err());
			assert!(Session::set_keys(Origin::signed(1), UintAuthorityId(10), vec![]).is_ok());

			// is fine now that 1 has migrated off.
			assert!(Session::set_keys(Origin::signed(4), UintAuthorityId(1), vec![]).is_ok());
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
