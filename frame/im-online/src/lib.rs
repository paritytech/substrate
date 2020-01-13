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

//! # I'm online Module
//!
//! If the local node is a validator (i.e. contains an authority key), this module
//! gossips a heartbeat transaction with each new session. The heartbeat functions
//! as a simple mechanism to signal that the node is online in the current era.
//!
//! Received heartbeats are tracked for one era and reset with each new era. The
//! module exposes two public functions to query if a heartbeat has been received
//! in the current era or session.
//!
//! The heartbeat is a signed transaction, which was signed using the session key
//! and includes the recent best block number of the local validators chain as well
//! as the [NetworkState](../../client/offchain/struct.NetworkState.html).
//! It is submitted as an Unsigned Transaction via off-chain workers.
//!
//! - [`im_online::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `is_online` - True if the validator sent a heartbeat in the current session.
//!
//! ## Usage
//!
//! ```
//! use frame_support::{decl_module, dispatch};
//! use frame_system::{self as system, ensure_signed};
//! use pallet_im_online::{self as im_online};
//!
//! pub trait Trait: im_online::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn is_online(origin, authority_index: u32) -> dispatch::DispatchResult {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _is_online = <im_online::Module<T>>::is_online(authority_index);
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```
//!
//! ## Dependencies
//!
//! This module depends on the [Session module](../pallet_session/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

mod mock;
mod tests;

use sp_application_crypto::RuntimeAppPublic;
use codec::{Encode, Decode};
use sp_core::offchain::{OpaqueNetworkState, StorageKind};
use sp_std::prelude::*;
use sp_std::convert::TryInto;
use pallet_session::historical::IdentificationTuple;
use sp_runtime::{
	RuntimeDebug,
	traits::{Convert, Member, Printable, Saturating}, Perbill,
	transaction_validity::{
		TransactionValidity, ValidTransaction, InvalidTransaction,
		TransactionPriority,
	},
};
use sp_staking::{
	SessionIndex,
	offence::{ReportOffence, Offence, Kind},
};
use frame_support::{
	decl_module, decl_event, decl_storage, print, Parameter, debug, decl_error,
	traits::Get,
};
use frame_system::{self as system, ensure_none};
use frame_system::offchain::SubmitUnsignedTransaction;

pub mod sr25519 {
	mod app_sr25519 {
		use sp_application_crypto::{app_crypto, key_types::IM_ONLINE, sr25519};
		app_crypto!(sr25519, IM_ONLINE);
	}

	/// An i'm online keypair using sr25519 as its crypto.
	#[cfg(feature = "std")]
	pub type AuthorityPair = app_sr25519::Pair;

	/// An i'm online signature using sr25519 as its crypto.
	pub type AuthoritySignature = app_sr25519::Signature;

	/// An i'm online identifier using sr25519 as its crypto.
	pub type AuthorityId = app_sr25519::Public;
}

pub mod ed25519 {
	mod app_ed25519 {
		use sp_application_crypto::{app_crypto, key_types::IM_ONLINE, ed25519};
		app_crypto!(ed25519, IM_ONLINE);
	}

	/// An i'm online keypair using ed25519 as its crypto.
	#[cfg(feature = "std")]
	pub type AuthorityPair = app_ed25519::Pair;

	/// An i'm online signature using ed25519 as its crypto.
	pub type AuthoritySignature = app_ed25519::Signature;

	/// An i'm online identifier using ed25519 as its crypto.
	pub type AuthorityId = app_ed25519::Public;
}

/// The local storage database key under which the worker progress status
/// is tracked.
const DB_KEY: &[u8] = b"parity/im-online-worker-status";

/// It's important to persist the worker state, since e.g. the
/// server could be restarted while starting the gossip process, but before
/// finishing it. With every execution of the off-chain worker we check
/// if we need to recover and resume gossipping or if there is already
/// another off-chain worker in the process of gossipping.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
struct WorkerStatus<BlockNumber> {
	done: bool,
	gossipping_at: BlockNumber,
}

/// Error which may occur while executing the off-chain code.
#[derive(RuntimeDebug)]
enum OffchainErr {
	DecodeWorkerStatus,
	FailedSigning,
	NetworkState,
	SubmitTransaction,
}

impl Printable for OffchainErr {
	fn print(&self) {
		match self {
			OffchainErr::DecodeWorkerStatus => print("Offchain error: decoding WorkerStatus failed!"),
			OffchainErr::FailedSigning => print("Offchain error: signing failed!"),
			OffchainErr::NetworkState => print("Offchain error: fetching network state failed!"),
			OffchainErr::SubmitTransaction => print("Offchain error: submitting transaction failed!"),
		}
	}
}

pub type AuthIndex = u32;

/// Heartbeat which is sent/received.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct Heartbeat<BlockNumber>
	where BlockNumber: PartialEq + Eq + Decode + Encode,
{
	/// Block number at the time heartbeat is created..
	pub block_number: BlockNumber,
	/// A state of local network (peer id and external addresses)
	pub network_state: OpaqueNetworkState,
	/// Index of the current session.
	pub session_index: SessionIndex,
	/// An index of the authority on the list of validators.
	pub authority_index: AuthIndex,
}

pub trait Trait: frame_system::Trait + pallet_session::historical::Trait {
	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + RuntimeAppPublic + Default + Ord;

	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as frame_system::Trait>::Event>;

	/// A dispatchable call type.
	type Call: From<Call<Self>>;

	/// A transaction submitter.
	type SubmitTransaction: SubmitUnsignedTransaction<Self, <Self as Trait>::Call>;

	/// An expected duration of the session.
	///
	/// This parameter is used to determine the longevity of `heartbeat` transaction
	/// and a rough time when the heartbeat should be sent.
	type SessionDuration: Get<Self::BlockNumber>;

	/// A type that gives us the ability to submit unresponsiveness offence reports.
	type ReportUnresponsiveness:
		ReportOffence<
			Self::AccountId,
			IdentificationTuple<Self>,
			UnresponsivenessOffence<IdentificationTuple<Self>>,
		>;
}

decl_event!(
	pub enum Event<T> where
		<T as Trait>::AuthorityId,
		IdentificationTuple = IdentificationTuple<T>,
	{
		/// A new heartbeat was received from `AuthorityId`
		HeartbeatReceived(AuthorityId),
		/// At the end of the session, no offence was committed.
		AllGood,
		/// At the end of the session, at least once validator was found to be offline.
		SomeOffline(Vec<IdentificationTuple>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as ImOnline {
		/// The block number when we should gossip.
		GossipAt get(fn gossip_at): T::BlockNumber;

		/// The current set of keys that may issue a heartbeat.
		Keys get(fn keys): Vec<T::AuthorityId>;

		/// For each session index, we keep a mapping of `AuthIndex`
		/// to `offchain::OpaqueNetworkState`.
		ReceivedHeartbeats get(fn received_heartbeats): double_map SessionIndex, AuthIndex
			=> Option<Vec<u8>>;

		/// For each session index, we keep a mapping of `T::ValidatorId` to the
		/// number of blocks authored by the given authority.
		AuthoredBlocks get(fn authored_blocks): double_map SessionIndex, T::ValidatorId => u32;
	}
	add_extra_genesis {
		config(keys): Vec<T::AuthorityId>;
		build(|config| Module::<T>::initialize_keys(&config.keys))
	}
}

decl_error! {
	/// Error for the im-online module.
	pub enum Error for Module<T: Trait> {
		/// Non existent public key.
		InvalidKey,
		/// Duplicated heartbeat.
		DuplicatedHeartbeat,
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		type Error = Error<T>;

		fn deposit_event() = default;

		fn heartbeat(
			origin,
			heartbeat: Heartbeat<T::BlockNumber>,
			// since signature verification is done in `validate_unsigned`
			// we can skip doing it here again.
			_signature: <T::AuthorityId as RuntimeAppPublic>::Signature
		) {
			ensure_none(origin)?;

			let current_session = <pallet_session::Module<T>>::current_index();
			let exists = <ReceivedHeartbeats>::exists(
				&current_session,
				&heartbeat.authority_index
			);
			let keys = Keys::<T>::get();
			let public = keys.get(heartbeat.authority_index as usize);
			if let (false, Some(public)) = (exists, public) {
				Self::deposit_event(Event::<T>::HeartbeatReceived(public.clone()));

				let network_state = heartbeat.network_state.encode();
				<ReceivedHeartbeats>::insert(
					&current_session,
					&heartbeat.authority_index,
					&network_state
				);
			} else if exists {
				Err(Error::<T>::DuplicatedHeartbeat)?
			} else {
				Err(Error::<T>::InvalidKey)?
			}
		}

		// Runs after every block.
		fn offchain_worker(now: T::BlockNumber) {
			debug::RuntimeLogger::init();

			// Only send messages if we are a potential validator.
			if sp_io::offchain::is_validator() {
				Self::offchain(now);
			}
		}
	}
}

/// Keep track of number of authored blocks per authority, uncles are counted as
/// well since they're a valid proof of onlineness.
impl<T: Trait + pallet_authorship::Trait> pallet_authorship::EventHandler<T::ValidatorId, T::BlockNumber> for Module<T> {
	fn note_author(author: T::ValidatorId) {
		Self::note_authorship(author);
	}

	fn note_uncle(author: T::ValidatorId, _age: T::BlockNumber) {
		Self::note_authorship(author);
	}
}

impl<T: Trait> Module<T> {
	/// Returns `true` if a heartbeat has been received for the authority at
	/// `authority_index` in the authorities series or if the authority has
	/// authored at least one block, during the current session. Otherwise
	/// `false`.
	pub fn is_online(authority_index: AuthIndex) -> bool {
		let current_validators = <pallet_session::Module<T>>::validators();

		if authority_index >= current_validators.len() as u32 {
			return false;
		}

		let authority = &current_validators[authority_index as usize];

		Self::is_online_aux(authority_index, authority)
	}

	fn is_online_aux(authority_index: AuthIndex, authority: &T::ValidatorId) -> bool {
		let current_session = <pallet_session::Module<T>>::current_index();

		<ReceivedHeartbeats>::exists(&current_session, &authority_index) ||
			<AuthoredBlocks<T>>::get(
				&current_session,
				authority,
			) != 0
	}

	/// Returns `true` if a heartbeat has been received for the authority at `authority_index` in
	/// the authorities series, during the current session. Otherwise `false`.
	pub fn received_heartbeat_in_current_session(authority_index: AuthIndex) -> bool {
		let current_session = <pallet_session::Module<T>>::current_index();
		<ReceivedHeartbeats>::exists(&current_session, &authority_index)
	}

	/// Note that the given authority has authored a block in the current session.
	fn note_authorship(author: T::ValidatorId) {
		let current_session = <pallet_session::Module<T>>::current_index();

		<AuthoredBlocks<T>>::mutate(
			&current_session,
			author,
			|authored| *authored += 1,
		);
	}

	pub(crate) fn offchain(now: T::BlockNumber) {
		let next_gossip = <GossipAt<T>>::get();
		let check = Self::check_not_yet_gossipped(now, next_gossip);
		let (curr_worker_status, not_yet_gossipped) = match check {
			Ok((s, v)) => (s, v),
			Err(err) => {
				print(err);
				return;
			},
		};
		if next_gossip < now && not_yet_gossipped {
			let value_set = Self::compare_and_set_worker_status(now, false, curr_worker_status);
			if !value_set {
				// value could not be set in local storage, since the value was
				// different from `curr_worker_status`. this indicates that
				// another worker was running in parallel.
				return;
			}

			match Self::do_gossip_at(now) {
				Ok(_) => {},
				Err(err) => print(err),
			}
		} else {
			debug::native::debug!(
				target: "imonline",
				"Skipping gossip at: {:?} >= {:?} || {:?}",
				next_gossip,
				now,
				if not_yet_gossipped { "not gossipped" } else { "gossipped" }
			);
		}
	}

	fn do_gossip_at(block_number: T::BlockNumber) -> Result<(), OffchainErr> {
		// we run only when a local authority key is configured
		let authorities = Keys::<T>::get();
		let mut results = Vec::new();
		let mut local_keys = T::AuthorityId::all();
		local_keys.sort();

		for (authority_index, key) in authorities.into_iter()
			.enumerate()
			.filter_map(|(index, authority)| {
				local_keys.binary_search(&authority)
					.ok()
					.map(|location| (index as u32, &local_keys[location]))
			})
		{
			if Self::is_online(authority_index) {
				debug::native::info!(
					target: "imonline",
					"[index: {:?}] Skipping sending heartbeat at block: {:?}. Already online.",
					authority_index,
					block_number
				);
				continue;
			}

			let network_state = sp_io::offchain::network_state()
				.map_err(|_| OffchainErr::NetworkState)?;
			let heartbeat_data = Heartbeat {
				block_number,
				network_state,
				session_index: <pallet_session::Module<T>>::current_index(),
				authority_index,
			};

			let signature = key.sign(&heartbeat_data.encode()).ok_or(OffchainErr::FailedSigning)?;
			let call = Call::heartbeat(heartbeat_data, signature);

			debug::info!(
				target: "imonline",
				"[index: {:?}] Reporting im-online at block: {:?}",
				authority_index,
				block_number
			);

			results.push(
				T::SubmitTransaction::submit_unsigned(call)
					.map_err(|_| OffchainErr::SubmitTransaction)
			);
		}

		// fail only after trying all keys.
		results.into_iter().collect::<Result<Vec<_>, OffchainErr>>()?;

		// once finished we set the worker status without comparing
		// if the existing value changed in the meantime. this is
		// because at this point the heartbeat was definitely submitted.
		Self::set_worker_status(block_number, true);

		Ok(())
	}

	fn compare_and_set_worker_status(
		gossipping_at: T::BlockNumber,
		done: bool,
		curr_worker_status: Option<Vec<u8>>,
	) -> bool {
		let enc = WorkerStatus {
			done,
			gossipping_at,
		};
		sp_io::offchain::local_storage_compare_and_set(
			StorageKind::PERSISTENT,
			DB_KEY,
			curr_worker_status,
			&enc.encode()
		)
	}

	fn set_worker_status(
		gossipping_at: T::BlockNumber,
		done: bool,
	) {
		let enc = WorkerStatus {
			done,
			gossipping_at,
		};
		sp_io::offchain::local_storage_set(StorageKind::PERSISTENT, DB_KEY, &enc.encode());
	}

	// Checks if a heartbeat gossip already occurred at this block number.
	// Returns a tuple of `(current worker status, bool)`, whereby the bool
	// is true if not yet gossipped.
	fn check_not_yet_gossipped(
		now: T::BlockNumber,
		next_gossip: T::BlockNumber,
	) -> Result<(Option<Vec<u8>>, bool), OffchainErr> {
		let last_gossip = sp_io::offchain::local_storage_get(StorageKind::PERSISTENT, DB_KEY);
		match last_gossip {
			Some(last) => {
				let worker_status: WorkerStatus<T::BlockNumber> = Decode::decode(&mut &last[..])
					.map_err(|_| OffchainErr::DecodeWorkerStatus)?;

				let was_aborted = !worker_status.done && worker_status.gossipping_at < now;

				// another off-chain worker is currently in the process of submitting
				let already_submitting =
					!worker_status.done && worker_status.gossipping_at == now;

				let not_yet_gossipped =
					worker_status.done && worker_status.gossipping_at < next_gossip;

				let ret = (was_aborted && !already_submitting) || not_yet_gossipped;
				Ok((Some(last), ret))
			},
			None => Ok((None, true)),
		}
	}

	fn initialize_keys(keys: &[T::AuthorityId]) {
		if !keys.is_empty() {
			assert!(Keys::<T>::get().is_empty(), "Keys are already initialized!");
			Keys::<T>::put(keys);
		}
	}
}

impl<T: Trait> sp_runtime::BoundToRuntimeAppPublic for Module<T> {
	type Public = T::AuthorityId;
}

impl<T: Trait> pallet_session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = T::AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		let keys = validators.map(|x| x.1).collect::<Vec<_>>();
		Self::initialize_keys(&keys);
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, _queued_validators: I)
		where I: Iterator<Item=(&'a T::AccountId, T::AuthorityId)>
	{
		// Tell the offchain worker to start making the next session's heartbeats.
		// Since we consider producing blocks as being online,
		// the hearbeat is defered a bit to prevent spaming.
		let block_number = <frame_system::Module<T>>::block_number();
		let half_session = T::SessionDuration::get() / 2.into();
		<GossipAt<T>>::put(block_number + half_session);

		// Remember who the authorities are for the new session.
		Keys::<T>::put(validators.map(|x| x.1).collect::<Vec<_>>());
	}

	fn on_before_session_ending() {
		let session_index = <pallet_session::Module<T>>::current_index();
		let keys = Keys::<T>::get();
		let current_validators = <pallet_session::Module<T>>::validators();

		let offenders = current_validators.into_iter().enumerate()
			.filter(|(index, id)|
				!Self::is_online_aux(*index as u32, id)
			).filter_map(|(_, id)|
				T::FullIdentificationOf::convert(id.clone()).map(|full_id| (id, full_id))
			).collect::<Vec<IdentificationTuple<T>>>();

		// Remove all received heartbeats and number of authored blocks from the
		// current session, they have already been processed and won't be needed
		// anymore.
		<ReceivedHeartbeats>::remove_prefix(&<pallet_session::Module<T>>::current_index());
		<AuthoredBlocks<T>>::remove_prefix(&<pallet_session::Module<T>>::current_index());

		if offenders.is_empty() {
			Self::deposit_event(RawEvent::AllGood);
		} else {
			Self::deposit_event(RawEvent::SomeOffline(offenders.clone()));

			let validator_set_count = keys.len() as u32;
			let offence = UnresponsivenessOffence { session_index, validator_set_count, offenders };
			T::ReportUnresponsiveness::report_offence(vec![], offence);
		}
	}

	fn on_disabled(_i: usize) {
		// ignore
	}
}

#[allow(deprecated)]
impl<T: Trait> frame_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(call: &Self::Call) -> TransactionValidity {
		if let Call::heartbeat(heartbeat, signature) = call {
			if <Module<T>>::is_online(heartbeat.authority_index) {
				// we already received a heartbeat for this authority
				return InvalidTransaction::Stale.into();
			}

			// check if session index from heartbeat is recent
			let current_session = <pallet_session::Module<T>>::current_index();
			if heartbeat.session_index != current_session {
				return InvalidTransaction::Stale.into();
			}

			// verify that the incoming (unverified) pubkey is actually an authority id
			let keys = Keys::<T>::get();
			let authority_id = match keys.get(heartbeat.authority_index as usize) {
				Some(id) => id,
				None => return InvalidTransaction::BadProof.into(),
			};

			// check signature (this is expensive so we do it last).
			let signature_valid = heartbeat.using_encoded(|encoded_heartbeat| {
				authority_id.verify(&encoded_heartbeat, &signature)
			});

			if !signature_valid {
				return InvalidTransaction::BadProof.into();
			}

			Ok(ValidTransaction {
				priority: TransactionPriority::max_value(),
				requires: vec![],
				provides: vec![(current_session, authority_id).encode()],
				longevity: TryInto::<u64>::try_into(T::SessionDuration::get() / 2.into()).unwrap_or(64_u64),
				propagate: true,
			})
		} else {
			InvalidTransaction::Call.into()
		}
	}
}

/// An offence that is filed if a validator didn't send a heartbeat message.
#[derive(RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Clone, PartialEq, Eq))]
pub struct UnresponsivenessOffence<Offender> {
	/// The current session index in which we report the unresponsive validators.
	///
	/// It acts as a time measure for unresponsiveness reports and effectively will always point
	/// at the end of the session.
	session_index: SessionIndex,
	/// The size of the validator set in current session/era.
	validator_set_count: u32,
	/// Authorities that were unresponsive during the current era.
	offenders: Vec<Offender>,
}

impl<Offender: Clone> Offence<Offender> for UnresponsivenessOffence<Offender> {
	const ID: Kind = *b"im-online:offlin";
	type TimeSlot = SessionIndex;

	fn offenders(&self) -> Vec<Offender> {
		self.offenders.clone()
	}

	fn session_index(&self) -> SessionIndex {
		self.session_index
	}

	fn validator_set_count(&self) -> u32 {
		self.validator_set_count
	}

	fn time_slot(&self) -> Self::TimeSlot {
		self.session_index
	}

	fn slash_fraction(offenders: u32, validator_set_count: u32) -> Perbill {
		// the formula is min((3 * (k - (n / 10 + 1))) / n, 1) * 0.07
		// basically, 10% can be offline with no slash, but after that, it linearly climbs up to 7%
		// when 13/30 are offline (around 5% when 1/3 are offline).
		if let Some(threshold) = offenders.checked_sub(validator_set_count / 10 + 1) {
			let x = Perbill::from_rational_approximation(3 * threshold, validator_set_count);
			x.saturating_mul(Perbill::from_percent(7))
		} else {
			Perbill::default()
		}
	}
}
