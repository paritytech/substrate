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
//! as the [NetworkState](../../core/offchain/struct.NetworkState.html).
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
//! - `is_online_in_current_era` - True if the validator sent a heartbeat in the current era.
//! - `is_online_in_current_session` - True if the validator sent a heartbeat in the current session.
//!
//! ## Usage
//!
//! ```
//! use srml_support::{decl_module, dispatch::Result};
//! use system::ensure_signed;
//! use srml_im_online::{self as im_online};
//!
//! pub trait Trait: im_online::Trait {}
//!
//! decl_module! {
//! 	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
//! 		pub fn is_online(origin, authority_id: T::AuthorityId) -> Result {
//! 			let _sender = ensure_signed(origin)?;
//! 			let _is_online = <im_online::Module<T>>::is_online_in_current_era(&authority_id);
//! 			Ok(())
//! 		}
//! 	}
//! }
//! # fn main() { }
//! ```
//!
//! ## Dependencies
//!
//! This module depends on the [Session module](../srml_session/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use primitives::{
	crypto::TypedKey, offchain::CryptoKey,
	offchain::OpaqueNetworkState,
	offchain::StorageKind,
	sr25519, ed25519,
};
use parity_codec::{Encode, Decode};
use sr_primitives::{
	ApplyError, traits::{Member, IsMember, Extrinsic as ExtrinsicT},
	transaction_validity::{TransactionValidity, TransactionLongevity, ValidTransaction},
};
use rstd::prelude::*;
use session::SessionIndex;
use sr_io::Printable;
use srml_support::{
	Parameter, StorageValue, decl_module, decl_event, decl_storage,
	traits::Get, StorageDoubleMap, print,
};
use system::ensure_none;

// The local storage database key under which the worker progress status
// is tracked.
const DB_KEY: &[u8] = b"srml/im-online-worker-status";

// It's important to persist the worker state, since e.g. the
// server could be restarted while starting the gossip process, but before
// finishing it. With every execution of the off-chain worker we check
// if we need to recover and resume gossipping or if there is already
// another off-chain worker in the process of gossipping.
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
struct WorkerStatus<BlockNumber> {
	done: bool,
	gossipping_at: BlockNumber,
}

// Error which may occur while executing the off-chain code.
enum OffchainErr {
	DecodeAuthorityId,
	DecodeWorkerStatus,
	ExtrinsicCreation,
	FailedSigning,
	NetworkState,
	SubmitTransaction,
}

impl Printable for OffchainErr {
	fn print(self) {
		match self {
			OffchainErr::DecodeAuthorityId => print("Offchain error: decoding AuthorityId failed!"),
			OffchainErr::DecodeWorkerStatus => print("Offchain error: decoding WorkerStatus failed!"),
			OffchainErr::ExtrinsicCreation => print("Offchain error: extrinsic creation failed!"),
			OffchainErr::FailedSigning => print("Offchain error: signing failed!"),
			OffchainErr::NetworkState => print("Offchain error: fetching network state failed!"),
			OffchainErr::SubmitTransaction => print("Offchain error: submitting transaction failed!"),
		}
	}
}

/// Heartbeat which is send/received.
#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Heartbeat<BlockNumber, AuthorityId>
	where BlockNumber: PartialEq + Eq + Decode + Encode,
{
	block_number: BlockNumber,
	network_state: OpaqueNetworkState,
	session_index: session::SessionIndex,
	authority_id: AuthorityId,
}

pub trait Trait: system::Trait + session::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	/// The function call.
	type Call: From<Call<Self>>;

	/// A extrinsic right from the external world. This is unchecked and so
	/// can contain a signature.
	type UncheckedExtrinsic: ExtrinsicT<Call=Self::Call> + Encode + Decode;

	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + Default + TypedKey + Decode + Encode + AsRef<[u8]>;

	/// Number of sessions per era.
	type SessionsPerEra: Get<SessionIndex>;

	/// Determine if an `AuthorityId` is a valid authority.
	type IsValidAuthorityId: IsMember<Self::AuthorityId>;
}

decl_event!(
	pub enum Event<T> where
		<T as system::Trait>::BlockNumber,
		<T as Trait>::AuthorityId
	{
		/// A new heartbeat was received at this `BlockNumber` from `AuthorityId`
		HeartbeatReceived(BlockNumber, AuthorityId),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as ImOnline {
		// The block number when we should gossip.
		GossipAt get(gossip_at) config(): T::BlockNumber;

		// The session index when the last new era started.
		LastNewEraStart get(last_new_era_start) config(): Option<session::SessionIndex>;

		// For each session index we keep a mapping of `AuthorityId` to
		// `offchain::OpaqueNetworkState`.
		ReceivedHeartbeats get(received_heartbeats): double_map session::SessionIndex,
			blake2_256(T::AuthorityId) => Vec<u8>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Number of sessions per era.
		const SessionsPerEra: session::SessionIndex = T::SessionsPerEra::get();

		fn deposit_event<T>() = default;

		fn heartbeat(
			origin,
			heartbeat: Heartbeat<T::BlockNumber, T::AuthorityId>,
			_signature: Vec<u8>
		) {
			ensure_none(origin)?;

			let current_session = <session::Module<T>>::current_index();
			let exists = <ReceivedHeartbeats<T>>::exists(&current_session, &heartbeat.authority_id);
			if !exists {
				let now = <system::Module<T>>::block_number();
				Self::deposit_event(RawEvent::HeartbeatReceived(now, heartbeat.authority_id.clone()));

				let network_state = heartbeat.network_state.encode();
				<ReceivedHeartbeats<T>>::insert(&current_session, &heartbeat.authority_id, &network_state);
			}
		}

		// Runs after every block.
		fn offchain_worker(now: T::BlockNumber) {
			fn gossip_at<T: Trait>(block_number: T::BlockNumber) -> Result<(), OffchainErr> {
				// we run only when a local authority key is configured
				if let Ok(key) = sr_io::pubkey(CryptoKey::AuthorityKey) {
					let authority_id = <T as Trait>::AuthorityId::decode(&mut &key[..])
						.ok_or(OffchainErr::DecodeAuthorityId)?;
					let network_state =
						sr_io::network_state().map_err(|_| OffchainErr::NetworkState)?;
					let heartbeat_data = Heartbeat {
						block_number,
						network_state,
						session_index: <session::Module<T>>::current_index(),
						authority_id,
					};

					let signature = sr_io::sign(CryptoKey::AuthorityKey, &heartbeat_data.encode())
						.map_err(|_| OffchainErr::FailedSigning)?;
					let call = Call::heartbeat(heartbeat_data, signature);
					let ex = T::UncheckedExtrinsic::new_unsigned(call.into())
						.ok_or(OffchainErr::ExtrinsicCreation)?;
					sr_io::submit_transaction(&ex)
						.map_err(|_| OffchainErr::SubmitTransaction)?;

					// once finished we set the worker status without comparing
					// if the existing value changed in the meantime. this is
					// because at this point the heartbeat was definitely submitted.
					set_worker_status::<T>(block_number, true);
				}
				Ok(())
			}

			fn compare_and_set_worker_status<T: Trait>(
				gossipping_at: T::BlockNumber,
				done: bool,
				curr_worker_status: Option<Vec<u8>>,
			) -> bool {
				let enc = WorkerStatus {
					done,
					gossipping_at,
				};
				sr_io::local_storage_compare_and_set(
					StorageKind::PERSISTENT,
					DB_KEY,
					curr_worker_status.as_ref().map(Vec::as_slice),
					&enc.encode()
				)
			}

			fn set_worker_status<T: Trait>(
				gossipping_at: T::BlockNumber,
				done: bool,
			) {
				let enc = WorkerStatus {
					done,
					gossipping_at,
				};
				sr_io::local_storage_set(
					StorageKind::PERSISTENT, DB_KEY, &enc.encode());
			}

			// Checks if a heartbeat gossip already occurred at this block number.
			// Returns a tuple of `(current worker status, bool)`, whereby the bool
			// is true if not yet gossipped.
			fn check_not_yet_gossipped<T: Trait>(
				now: T::BlockNumber,
				next_gossip: T::BlockNumber,
			) -> Result<(Option<Vec<u8>>, bool), OffchainErr> {
				let last_gossip = sr_io::local_storage_get(StorageKind::PERSISTENT, DB_KEY);
				match last_gossip {
					Some(last) => {
						let worker_status: WorkerStatus<T::BlockNumber> = Decode::decode(&mut &last[..])
							.ok_or(OffchainErr::DecodeWorkerStatus)?;

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

			let next_gossip = <GossipAt<T>>::get();
			let check = check_not_yet_gossipped::<T>(now, next_gossip);
			let (curr_worker_status, not_yet_gossipped) = match check {
				Ok((s, v)) => (s, v),
				Err(err) => {
					print(err);
					return;
				},
			};
			if next_gossip < now && not_yet_gossipped {
				let value_set = compare_and_set_worker_status::<T>(now, false, curr_worker_status);
				if !value_set {
					// value could not be set in local storage, since the value was
					// different from `curr_worker_status`. this indicates that
					// another worker was running in parallel.
					return;
				}

				match gossip_at::<T>(now) {
					Ok(_) => {},
					Err(err) => print(err),
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Returns `true` if a heartbeat has been received for `AuthorityId`
	/// during the current era. Otherwise `false`.
	pub fn is_online_in_current_era(authority_id: &T::AuthorityId) -> bool {
		let curr = <session::Module<T>>::current_index();
		match LastNewEraStart::get() {
			Some(start) => {
				// iterate over every session
				for index in start..curr  {
					if <ReceivedHeartbeats<T>>::exists(&index, authority_id) {
						return true;
					}
				}
				false
			},
			None => <ReceivedHeartbeats<T>>::exists(&curr, authority_id),
		}
	}

	/// Returns `true` if a heartbeat has been received for `AuthorityId`
	/// during the current session. Otherwise `false`.
	pub fn is_online_in_current_session(authority_id: &T::AuthorityId) -> bool {
		let current_session = <session::Module<T>>::current_index();
		<ReceivedHeartbeats<T>>::exists(&current_session, authority_id)
	}

	/// Session has just changed.
	fn new_session() {
		let now = <system::Module<T>>::block_number();
		<GossipAt<T>>::put(now);

		let current_session = <session::Module<T>>::current_index();

		match LastNewEraStart::get() {
			Some(last_new_era_start) => {
				let sessions_per_era = T::SessionsPerEra::get();

				let new_era = current_session - last_new_era_start > sessions_per_era;
				if new_era {
					LastNewEraStart::put(current_session);
					Self::remove_heartbeats();
				}
			},
			None => LastNewEraStart::put(current_session),
		};
	}

	// Remove all stored heartbeats.
	fn remove_heartbeats() {
		let curr = <session::Module<T>>::current_index();
		match LastNewEraStart::get() {
			Some(start) => {
				for index in start..curr {
					<ReceivedHeartbeats<T>>::remove_prefix(&index);
				}
			},
			None => <ReceivedHeartbeats<T>>::remove_prefix(&curr),
		}
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = <T as Trait>::AuthorityId;

	fn on_new_session<'a, I: 'a>(_changed: bool, _validators: I, _next_validators: I) {
		Self::new_session();
	}

	fn on_disabled(_i: usize) {
		// ignore
	}
}

impl<T: Trait> srml_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(call: &Self::Call) -> srml_support::unsigned::TransactionValidity {
		if let Call::heartbeat(heartbeat, signature) = call {
			// verify that the incoming (unverified) pubkey is actually an authority id
			let is_authority = T::IsValidAuthorityId::is_member(&heartbeat.authority_id);
			if !is_authority {
				return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
			}

			if <Module<T>>::is_online_in_current_session(&heartbeat.authority_id) {
				// we already received a heartbeat for this authority
				return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
			}

			if signature.len() != 64 {
				return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
			}

			let signature = {
				  let mut array = [0; 64];
				  array.copy_from_slice(&signature); // panics if not enough, hence the check above
				  array
			};

			let encoded_heartbeat = heartbeat.encode();

			let signature_valid = match <T::AuthorityId as TypedKey>::KEY_TYPE {
				ed25519::Public::KEY_TYPE =>
					sr_io::ed25519_verify(&signature, &encoded_heartbeat, &heartbeat.authority_id),
				sr25519::Public::KEY_TYPE =>
					sr_io::sr25519_verify(&signature, &encoded_heartbeat, &heartbeat.authority_id),
				_ => return TransactionValidity::Invalid(ApplyError::BadSignature as i8),
			};

			if !signature_valid {
				return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
			}

			// check if session index from heartbeat is recent
			let current_session = <session::Module<T>>::current_index();
			if heartbeat.session_index < current_session {
				return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
			}

			return TransactionValidity::Valid(ValidTransaction {
				priority: 0,
				requires: vec![],
				provides: vec![encoded_heartbeat],
				longevity: TransactionLongevity::max_value(),
				propagate: true,
			})
		}
		TransactionValidity::Invalid(0)
	}
}
