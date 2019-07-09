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

//! # I'm online Module
//!
//! If the local node is a validator (i.e. contains an authority key), this module
//! gossips a heartbeat transaction with each new session. The heartbeat functions
//! as a simple mechanism to signal that the node is online in the current era.
//!
//! Received heartbeats are tracked for one era and reset with each new era. The
//! module exposes a public function `is_online_in_current_era(AuthorityId)` to query if a heartbeat
//! has been received in the current era.
//!
//! The heartbeat is a signed transaction, which was signed using the session key
//! and includes the recent best block number of the local validators chain as well
//! as the [LocalNetworkState](../../core/offchain/struct.LocalNetworkState.html).
//! It is submitted as an Unsigned Transaction via offchain workers.
//!
//! - [`im_online::Trait`](./trait.Trait.html)
//! - [`Call`](./enum.Call.html)
//! - [`Module`](./struct.Module.html)
//!
//! ## Interface
//!
//! ### Public Functions
//!
//! - `is_online_in_current_era` - Find out if the validator has sent a heartbeat during the current era.
//!
//! ## Usage
//!
//! TODO: will be done in follow-up once the API is set.
//!
//! ## Dependencies
//!
//! This module depends on the [Session module](../srml_session/index.html).

// Ensure we're `no_std` when compiling for Wasm.
#![cfg_attr(not(feature = "std"), no_std)]

use substrate_primitives::{crypto::TypedKey, offchain::CryptoKind};
use parity_codec::{Encode, Decode};
use primitives::{
	ApplyError, traits::{Member, Extrinsic as ExtrinsicT},
	transaction_validity::{TransactionValidity, TransactionLongevity},
};
use rstd::{prelude::*};
use session::SessionIndex;
use srml_support::{
	Parameter, StorageValue, decl_module, decl_event, decl_storage,
	traits::Get, StorageDoubleMap, print,
};
use system::ensure_none;

const PREFIX: u32 = 0;

pub trait Trait: system::Trait + session::Trait {
	/// The overarching event type.
	type Event: From<Event<Self>> + Into<<Self as system::Trait>::Event>;

	type Call: From<Call<Self>>;

	/// A extrinsic right from the external world. This is unchecked and so
	/// can contain a signature.
	type UncheckedExtrinsic: ExtrinsicT<Call=Self::Call> + Encode + Decode;

	/// The identifier type for an authority.
	type AuthorityId: Member + Parameter + Default + TypedKey + Decode + Encode + AsRef<[u8]>;

	/// Number of sessions per era.
	type SessionsPerEra: Get<SessionIndex>;

	/// The crypto used when looking up if a local authority id is configured.
	/// Must equal the crypto used in `AuthorityId`, otherwise no local key will
	/// be found.
	const CRYPTO_KIND: CryptoKind;

	/// Function to determine if an `AuthorityId` is a valid authority.
	fn is_valid_authority_id(authority_id: &Self::AuthorityId) -> bool;
}

decl_event!(
	pub enum Event<T> where
		<T as system::Trait>::BlockNumber,
		<T as Trait>::AuthorityId
	{
		HeartbeatReceived(BlockNumber, AuthorityId),
	}
);

#[derive(Encode, Decode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub struct Heartbeat<BlockNumber, AuthorityId>
	where BlockNumber: PartialEq + Eq + Decode + Encode,
{
	block_number: BlockNumber,
	network_state: Vec<u8>, // serialized `offchain::LocalNetworkState`
	session_index: session::SessionIndex,
	authority_id: AuthorityId,
}

enum OffchainErr {
	DecodeAuthorityId,
	ExtrinsicCreation,
	FailedSigning,
	LocalNetworkState,
	SubmitTransaction,
}

decl_storage! {
	trait Store for Module<T: Trait> as ImOnline {
		// The block number when we should gossip.
		GossipAt get(gossip_at) config(): T::BlockNumber;

		// The session index when the last new era started.
		LastNewEraStart get(last_new_era_start) config(): Option<session::SessionIndex>;

		// Mapping of AuthorityId to the serialized struct `offchain::LocalNetworkState`.
		// We currently don't provide the deserialized struct, since the contained types
		// don't compile for wasm (and since there is currently no need).
		//
		// The `StorageMap` implementation currently doesn't provide an easy way to
		// clear the map, hence we use this workaround of a `double_map` with the
		// fixed `PREFIX` constant.
		ReceivedHeartbeats get(received_heartbeats) config(): double_map u32, blake2_256(T::AuthorityId) => Vec<u8>;
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

			let exists = <ReceivedHeartbeats<T>>::exists(PREFIX, &heartbeat.authority_id);
			if !exists {
				let now = <system::Module<T>>::block_number();
				Self::deposit_event(RawEvent::HeartbeatReceived(now, heartbeat.authority_id.clone()));

				<ReceivedHeartbeats<T>>::insert(PREFIX, &heartbeat.authority_id, heartbeat.network_state);
			}
		}

		// Runs after every block.
		fn offchain_worker(block_number: T::BlockNumber) {
			fn gossip<T: Trait>(block_number: T::BlockNumber) -> Result<(), OffchainErr> {
				match sr_io::local_authority_pubkey(<T as Trait>::CRYPTO_KIND) {
					Ok(key) => {
						let authority_id = <T as Trait>::AuthorityId::decode(&mut &key[..])
							.ok_or(OffchainErr::DecodeAuthorityId)?;
						let network_state =
							sr_io::local_network_state().map_err(|_| OffchainErr::LocalNetworkState)?;
						let heartbeat_data = Heartbeat {
							block_number,
							network_state,
							session_index: <session::Module<T>>::current_index(),
							authority_id,
						};

						match sr_io::sign(None, <T as Trait>::CRYPTO_KIND, &heartbeat_data.encode()) {
							Ok(signature) => {
								let call = Call::heartbeat(heartbeat_data, signature);
								let ex = T::UncheckedExtrinsic::new_unsigned(call.into())
									.ok_or(OffchainErr::ExtrinsicCreation)?;
								sr_io::submit_transaction(&ex)
									.map_err(|_| OffchainErr::SubmitTransaction)?;
								Ok(())
							},
							Err(_) => Err(OffchainErr::FailedSigning),
						}
					},
					Err(_) => {
						// we only run when a local authority key is configured
						Ok(())
					}
				}
			}

			let gossip_at = <GossipAt<T>>::get();
			let now = <system::Module<T>>::block_number();
			if gossip_at == now {
				match gossip::<T>(block_number) {
					Ok(_) => {},
					Err(_) => {
						print("Error in offchain worker!");
					},
				}
			}
		}
	}
}

impl<T: Trait> Module<T> {
	/// Returns `true` if a heartbeat has been received for `AuthorityId`
	/// during the current era. Otherwise `false`.
	pub fn is_online_in_current_era(authority_id: &T::AuthorityId) -> bool {
		<ReceivedHeartbeats<T>>::exists(PREFIX, authority_id)
	}

	/// Session has just changed.
	fn new_session() {
		let now = <system::Module<T>>::block_number();
		<GossipAt<T>>::put(now);

		let current_session = <session::Module<T>>::current_index();

		match LastNewEraStart::get() {
			Some(last_new_era_start) => {
				let sessions_per_era = T::SessionsPerEra::get();

				// clear map after each era
				let new_era = current_session - last_new_era_start > sessions_per_era;
				if new_era {
					LastNewEraStart::put(current_session);
					<ReceivedHeartbeats<T>>::remove_prefix(PREFIX);
				}
			},
			None => LastNewEraStart::put(current_session),
		};
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = <T as Trait>::AuthorityId;

	fn on_new_session<'a, I: 'a>(_changed: bool, _validators: I) {
		Self::new_session();
	}

	fn on_disabled(_i: usize) {
		// ignore
	}
}

impl<T: Trait> srml_support::unsigned::ValidateUnsigned for Module<T> {
	type Call = Call<T>;

	fn validate_unsigned(call: &Self::Call) -> srml_support::unsigned::TransactionValidity {
		match call {
			Call::heartbeat(heartbeat, signature) => {
				// verify that the incoming (unverified) pubkey is actually an authority id
				let is_authority = <T as Trait>::is_valid_authority_id(&heartbeat.authority_id);
				if !is_authority {
					return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
				}

				if signature.len() != 64 {
					return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
				}
				let mut array = [0; 64];
				let bytes = &signature[..64]; // panics if not enough, hence the check above
				array.copy_from_slice(bytes);

				let signature_valid = match <T as Trait>::CRYPTO_KIND {
					CryptoKind::Ed25519 =>
						sr_io::ed25519_verify(&array, &heartbeat.encode(), &heartbeat.authority_id),
					CryptoKind::Sr25519 =>
						sr_io::sr25519_verify(&array, &heartbeat.encode(), &heartbeat.authority_id),
				};
				if !signature_valid {
					return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
				}

				// check if session index from heartbeat is recent
				let current_session = <session::Module<T>>::current_index();
				if heartbeat.session_index < current_session {
					return TransactionValidity::Invalid(ApplyError::BadSignature as i8);
				}

				let transaction_tag = heartbeat.encode();
				srml_support::unsigned::TransactionValidity::Valid {
					priority: 0,
					requires: vec![],
					provides: vec![transaction_tag],
					longevity: TransactionLongevity::max_value(),
					propagate: true,
				}
			}
			_ => {
				// couldn't match
				TransactionValidity::Invalid(0)
			},
		}
	}
}
