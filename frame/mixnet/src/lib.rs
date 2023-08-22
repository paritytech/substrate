// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! This pallet is responsible for determining the current mixnet session and phase, and the
//! mixnode set for each session.

#![warn(missing_docs)]
#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	traits::{EstimateNextSessionRotation, Get, OneSessionHandler},
	BoundedVec,
};
use frame_system::{
	offchain::{SendTransactionTypes, SubmitTransaction},
	pallet_prelude::BlockNumberFor,
};
pub use pallet::*;
use scale_info::TypeInfo;
use serde::{Deserialize, Serialize};
use sp_application_crypto::RuntimeAppPublic;
use sp_arithmetic::traits::{CheckedSub, Saturating, UniqueSaturatedInto, Zero};
use sp_io::MultiRemovalResults;
use sp_mixnet::types::{
	AuthorityId, AuthoritySignature, KxPublic, Mixnode, MixnodesErr, PeerId, SessionIndex,
	SessionPhase, SessionStatus, KX_PUBLIC_SIZE,
};
use sp_runtime::RuntimeDebug;
use sp_std::{cmp::Ordering, vec::Vec};

const LOG_TARGET: &str = "runtime::mixnet";

/// Index of an authority in the authority list for a session.
pub type AuthorityIndex = u32;

////////////////////////////////////////////////////////////////////////////////
// Bounded mixnode type
////////////////////////////////////////////////////////////////////////////////

/// Like [`Mixnode`], but encoded size is bounded.
#[derive(
	Clone, Decode, Encode, MaxEncodedLen, PartialEq, TypeInfo, RuntimeDebug, Serialize, Deserialize,
)]
pub struct BoundedMixnode<ExternalAddresses> {
	/// Key-exchange public key for the mixnode.
	pub kx_public: KxPublic,
	/// libp2p peer ID of the mixnode.
	pub peer_id: PeerId,
	/// External addresses for the mixnode, in multiaddr format, UTF-8 encoded.
	pub external_addresses: ExternalAddresses,
}

impl<MaxExternalAddressSize, MaxExternalAddresses> Into<Mixnode>
	for BoundedMixnode<BoundedVec<BoundedVec<u8, MaxExternalAddressSize>, MaxExternalAddresses>>
{
	fn into(self) -> Mixnode {
		Mixnode {
			kx_public: self.kx_public,
			peer_id: self.peer_id,
			external_addresses: self
				.external_addresses
				.into_iter()
				.map(BoundedVec::into_inner)
				.collect(),
		}
	}
}

impl<MaxExternalAddressSize: Get<u32>, MaxExternalAddresses: Get<u32>> From<Mixnode>
	for BoundedMixnode<BoundedVec<BoundedVec<u8, MaxExternalAddressSize>, MaxExternalAddresses>>
{
	fn from(mixnode: Mixnode) -> Self {
		Self {
			kx_public: mixnode.kx_public,
			peer_id: mixnode.peer_id,
			external_addresses: mixnode
				.external_addresses
				.into_iter()
				.flat_map(|addr| match addr.try_into() {
					Ok(addr) => Some(addr),
					Err(addr) => {
						log::debug!(target: LOG_TARGET,
							"Mixnode external address {addr:x?} too long; discarding");
						None
					},
				})
				.take(MaxExternalAddresses::get() as usize)
				.collect::<Vec<_>>()
				.try_into()
				.expect("Excess external addresses discarded with take()"),
		}
	}
}

/// [`BoundedMixnode`] type for the given configuration.
pub type BoundedMixnodeFor<T> = BoundedMixnode<
	BoundedVec<
		BoundedVec<u8, <T as Config>::MaxExternalAddressSize>,
		<T as Config>::MaxExternalAddressesPerMixnode,
	>,
>;

////////////////////////////////////////////////////////////////////////////////
// Registration type
////////////////////////////////////////////////////////////////////////////////

/// A mixnode registration. A registration transaction is formed from one of these plus an
/// [`AuthoritySignature`].
#[derive(Clone, Decode, Encode, PartialEq, TypeInfo, RuntimeDebug)]
pub struct Registration<BlockNumber, BoundedMixnode> {
	/// Block number at the time of creation. When a registration transaction fails to make it on
	/// to the chain for whatever reason, we send out another one. We want this one to have a
	/// different hash in case the earlier transaction got banned somewhere; including the block
	/// number is a simple way of achieving this.
	pub block_number: BlockNumber,
	/// The session during which this registration should be processed. Note that on success the
	/// mixnode is registered for the _following_ session.
	pub session_index: SessionIndex,
	/// The index in the next session's authority list of the authority registering the mixnode.
	pub authority_index: AuthorityIndex,
	/// Mixnode information to register for the following session.
	pub mixnode: BoundedMixnode,
}

/// [`Registration`] type for the given configuration.
pub type RegistrationFor<T> = Registration<BlockNumberFor<T>, BoundedMixnodeFor<T>>;

////////////////////////////////////////////////////////////////////////////////
// Misc helper funcs
////////////////////////////////////////////////////////////////////////////////

fn check_removed_all(res: MultiRemovalResults) {
	debug_assert!(res.maybe_cursor.is_none());
}

fn twox<BlockNumber: UniqueSaturatedInto<u64>>(
	block_number: BlockNumber,
	kx_public: &KxPublic,
) -> u64 {
	let block_number: u64 = block_number.unique_saturated_into();
	let mut data = [0; 8 + KX_PUBLIC_SIZE];
	data[..8].copy_from_slice(&block_number.to_le_bytes());
	data[8..].copy_from_slice(kx_public);
	u64::from_le_bytes(sp_io::hashing::twox_64(&data))
}

////////////////////////////////////////////////////////////////////////////////
// The pallet
////////////////////////////////////////////////////////////////////////////////

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use super::*;
	use frame_support::pallet_prelude::*;
	use frame_system::pallet_prelude::*;

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	#[pallet::config]
	pub trait Config: frame_system::Config + SendTransactionTypes<Call<Self>> {
		/// The maximum number of authorities per session.
		#[pallet::constant]
		type MaxAuthorities: Get<AuthorityIndex>;

		/// The maximum size of one of a mixnode's external addresses.
		#[pallet::constant]
		type MaxExternalAddressSize: Get<u32>;

		/// The maximum number of external addresses for a mixnode.
		#[pallet::constant]
		type MaxExternalAddressesPerMixnode: Get<u32>;

		/// Session progress/length estimation. Used to determine when to send registration
		/// transactions and the longevity of these transactions.
		type NextSessionRotation: EstimateNextSessionRotation<BlockNumberFor<Self>>;

		/// Length of the first phase of each session (`CoverToCurrent`), in blocks.
		#[pallet::constant]
		type NumCoverToCurrentBlocks: Get<BlockNumberFor<Self>>;

		/// Length of the second phase of each session (`RequestsToCurrent`), in blocks.
		#[pallet::constant]
		type NumRequestsToCurrentBlocks: Get<BlockNumberFor<Self>>;

		/// Length of the third phase of each session (`CoverToPrev`), in blocks.
		#[pallet::constant]
		type NumCoverToPrevBlocks: Get<BlockNumberFor<Self>>;

		/// The number of "slack" blocks at the start of each session, during which
		/// [`maybe_register`](Pallet::maybe_register) will not attempt to post registration
		/// transactions.
		#[pallet::constant]
		type NumRegisterStartSlackBlocks: Get<BlockNumberFor<Self>>;

		/// The number of "slack" blocks at the end of each session.
		/// [`maybe_register`](Pallet::maybe_register) will try to register before this slack
		/// period, but may post registration transactions during the slack period as a last
		/// resort.
		#[pallet::constant]
		type NumRegisterEndSlackBlocks: Get<BlockNumberFor<Self>>;

		/// Priority of unsigned transactions used to register mixnodes.
		#[pallet::constant]
		type RegistrationPriority: Get<TransactionPriority>;

		/// Minimum number of mixnodes. If there are fewer than this many mixnodes registered for a
		/// session, the mixnet will not be active during the session.
		#[pallet::constant]
		type MinMixnodes: Get<u32>;
	}

	/// Index of the current session. This may be offset relative to the session index tracked by
	/// eg `pallet_session`; mixnet session indices are independent.
	#[pallet::storage]
	pub(crate) type CurrentSessionIndex<T> = StorageValue<_, SessionIndex, ValueQuery>;

	/// Block in which the current session started.
	#[pallet::storage]
	pub(crate) type CurrentSessionStartBlock<T> = StorageValue<_, BlockNumberFor<T>, ValueQuery>;

	/// Authority list for the next session.
	#[pallet::storage]
	pub(crate) type NextAuthorityIds<T> = StorageMap<_, Identity, AuthorityIndex, AuthorityId>;

	/// Mixnode sets by session index. Only the mixnode sets for the previous, current, and next
	/// sessions are kept; older sets are discarded.
	///
	/// The mixnodes in each set are keyed by authority index so we can easily check if an
	/// authority has registered a mixnode. The authority indices should only be used during
	/// registration; the authority indices for the very first session are made up.
	#[pallet::storage]
	pub(crate) type Mixnodes<T> =
		StorageDoubleMap<_, Identity, SessionIndex, Identity, AuthorityIndex, BoundedMixnodeFor<T>>;

	#[pallet::genesis_config]
	#[derive(frame_support::DefaultNoBound)]
	pub struct GenesisConfig<T: Config> {
		/// The mixnode set for the very first session.
		pub mixnodes: BoundedVec<BoundedMixnodeFor<T>, T::MaxAuthorities>,
	}

	#[pallet::genesis_build]
	impl<T: Config> BuildGenesisConfig for GenesisConfig<T> {
		fn build(&self) {
			assert!(
				Mixnodes::<T>::iter_prefix_values(0).next().is_none(),
				"Initial mixnodes already set"
			);
			for (i, mixnode) in self.mixnodes.iter().enumerate() {
				// We just make up authority indices here. This doesn't matter as authority indices
				// are only used during registration to check an authority doesn't register twice.
				Mixnodes::<T>::insert(0, i as AuthorityIndex, mixnode);
			}
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Register a mixnode for the following session.
		#[pallet::call_index(0)]
		#[pallet::weight(1)] // TODO
		pub fn register(
			origin: OriginFor<T>,
			registration: RegistrationFor<T>,
			_signature: AuthoritySignature,
		) -> DispatchResult {
			ensure_none(origin)?;

			// Checked by ValidateUnsigned
			debug_assert_eq!(registration.session_index, CurrentSessionIndex::<T>::get());
			debug_assert!(registration.authority_index < T::MaxAuthorities::get());

			Mixnodes::<T>::insert(
				// Registering for the _following_ session
				registration.session_index.wrapping_add(1),
				registration.authority_index,
				registration.mixnode,
			);

			Ok(())
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;

		fn validate_unsigned(_source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			let Self::Call::register { registration, signature } = call else {
				return InvalidTransaction::Call.into()
			};

			// Check session index matches
			match registration.session_index.cmp(&CurrentSessionIndex::<T>::get()) {
				Ordering::Greater => return InvalidTransaction::Future.into(),
				Ordering::Less => return InvalidTransaction::Stale.into(),
				Ordering::Equal => (),
			}

			// Check authority index is valid
			if registration.authority_index >= T::MaxAuthorities::get() {
				return InvalidTransaction::BadProof.into()
			}
			let Some(authority_id) = NextAuthorityIds::<T>::get(registration.authority_index)
			else {
				return InvalidTransaction::BadProof.into()
			};

			// Check the authority hasn't registered a mixnode yet
			if Self::already_registered(registration.session_index, registration.authority_index) {
				return InvalidTransaction::Stale.into()
			}

			// Check signature. Note that we don't use regular signed transactions for registration
			// as we don't want validators to have to pay to register. Spam is prevented by only
			// allowing one registration per session per validator (see above).
			let signature_ok = registration.using_encoded(|encoded_registration| {
				authority_id.verify(&encoded_registration, signature)
			});
			if !signature_ok {
				return InvalidTransaction::BadProof.into()
			}

			ValidTransaction::with_tag_prefix("MixnetRegistration")
				.priority(T::RegistrationPriority::get())
				// Include both authority index _and_ ID in tag in case of forks with different
				// authority lists
				.and_provides((
					registration.session_index,
					registration.authority_index,
					authority_id,
				))
				.longevity(
					(T::NextSessionRotation::average_session_length() / 2_u32.into())
						.try_into()
						.unwrap_or(64_u64),
				)
				.build()
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Returns the phase of the current session.
	fn session_phase() -> SessionPhase {
		let block_in_phase = frame_system::Pallet::<T>::block_number()
			.saturating_sub(CurrentSessionStartBlock::<T>::get());
		let Some(block_in_phase) = block_in_phase.checked_sub(&T::NumCoverToCurrentBlocks::get())
		else {
			return SessionPhase::CoverToCurrent
		};
		let Some(block_in_phase) =
			block_in_phase.checked_sub(&T::NumRequestsToCurrentBlocks::get())
		else {
			return SessionPhase::RequestsToCurrent
		};
		if block_in_phase < T::NumCoverToPrevBlocks::get() {
			SessionPhase::CoverToPrev
		} else {
			SessionPhase::DisconnectFromPrev
		}
	}

	/// Returns the index and phase of the current session.
	pub fn session_status() -> SessionStatus {
		SessionStatus {
			current_index: CurrentSessionIndex::<T>::get(),
			phase: Self::session_phase(),
		}
	}

	/// Returns the mixnode set for the given session (which should be either the previous or the
	/// current session).
	fn mixnodes(session_index: SessionIndex) -> Result<Vec<Mixnode>, MixnodesErr> {
		let mixnodes: Vec<_> =
			Mixnodes::<T>::iter_prefix_values(session_index).map(Into::into).collect();
		if mixnodes.len() < T::MinMixnodes::get() as usize {
			Err(MixnodesErr::InsufficientRegistrations {
				num: mixnodes.len() as u32,
				min: T::MinMixnodes::get(),
			})
		} else {
			Ok(mixnodes)
		}
	}

	/// Returns the mixnode set for the previous session.
	pub fn prev_mixnodes() -> Result<Vec<Mixnode>, MixnodesErr> {
		Self::mixnodes(CurrentSessionIndex::<T>::get().wrapping_sub(1))
	}

	/// Returns the mixnode set for the current session.
	pub fn current_mixnodes() -> Result<Vec<Mixnode>, MixnodesErr> {
		Self::mixnodes(CurrentSessionIndex::<T>::get())
	}

	/// Is now a good time to register, considering only session progress?
	fn should_register_by_session_progress(
		block_number: BlockNumberFor<T>,
		mixnode: &Mixnode,
	) -> bool {
		// At the start of each session there are some "slack" blocks during which we avoid
		// registering
		let block_in_session = block_number.saturating_sub(CurrentSessionStartBlock::<T>::get());
		if block_in_session < T::NumRegisterStartSlackBlocks::get() {
			return false
		}

		let (Some(end_block), _weight) =
			T::NextSessionRotation::estimate_next_session_rotation(block_number)
		else {
			// Things aren't going to work terribly well in this case as all the authorities will
			// just pile in after the slack period...
			return true
		};

		let remaining_blocks = end_block
			.saturating_sub(block_number)
			.saturating_sub(T::NumRegisterEndSlackBlocks::get());
		if remaining_blocks.is_zero() {
			// Into the slack time at the end of the session. Not necessarily too late;
			// registrations are accepted right up until the session ends.
			return true
		}

		// Want uniform distribution over the remaining blocks, so pick this block with probability
		// 1/remaining_blocks. maybe_register may be called multiple times per block; ensure the
		// same decision gets made each time by using a hash of the block number and the mixnode's
		// public key as the "random" source. This is slightly biased as remaining_blocks most
		// likely won't divide into 2^64, but it doesn't really matter...
		let random = twox(block_number, &mixnode.kx_public);
		(random % remaining_blocks.try_into().unwrap_or(u64::MAX)) == 0
	}

	fn next_local_authority() -> Option<(AuthorityIndex, AuthorityId)> {
		// In the case where multiple local IDs are in the next authority set, we just return the
		// first one. There's (currently at least) no point in registering multiple times.
		let mut local_ids = AuthorityId::all();
		local_ids.sort();
		NextAuthorityIds::<T>::iter().find(|(_index, id)| local_ids.binary_search(id).is_ok())
	}

	/// `session_index` should be the index of the current session. `authority_index` is the
	/// authority index in the _next_ session.
	fn already_registered(session_index: SessionIndex, authority_index: AuthorityIndex) -> bool {
		Mixnodes::<T>::contains_key(session_index.wrapping_add(1), authority_index)
	}

	/// Try to register a mixnode for the next session.
	///
	/// If a registration extrinsic is submitted, `true` is returned. The caller should avoid
	/// calling `maybe_register` again for a few blocks, to give the submitted extrinsic a chance
	/// to get included.
	///
	/// With the above exception, `maybe_register` is designed to be called every block. Most of
	/// the time it will not do anything, for example:
	///
	/// - If it is not an appropriate time to submit a registration extrinsic.
	/// - If the local node has already registered a mixnode for the next session.
	/// - If the local node is not permitted to register a mixnode for the next session.
	///
	/// `session_index` should match `session_status().current_index`; if it does not, `false` is
	/// returned immediately.
	pub fn maybe_register(session_index: SessionIndex, mixnode: Mixnode) -> bool {
		let current_session_index = CurrentSessionIndex::<T>::get();
		if session_index != current_session_index {
			log::debug!(
				target: LOG_TARGET,
				"Session {session_index} registration attempted, \
				but current session is {current_session_index}");
			return false
		}

		let block_number = frame_system::Pallet::<T>::block_number();
		if !Self::should_register_by_session_progress(block_number, &mixnode) {
			log::debug!(
				target: LOG_TARGET,
				"Waiting for the session to progress further before registering");
			return false
		}

		let Some((authority_index, authority_id)) = Self::next_local_authority() else {
			log::debug!(
				target: LOG_TARGET,
				"Not an authority in the next session; cannot register a mixnode");
			return false
		};

		if Self::already_registered(session_index, authority_index) {
			log::debug!(
				target: LOG_TARGET,
				"Already registered a mixnode for the next session");
			return false
		}

		let registration =
			Registration { block_number, session_index, authority_index, mixnode: mixnode.into() };
		let Some(signature) = authority_id.sign(&registration.encode()) else {
			log::error!(target: LOG_TARGET, "Failed to sign registration");
			return false
		};
		let call = Call::register { registration, signature };
		match SubmitTransaction::<T, Call<T>>::submit_unsigned_transaction(call.into()) {
			Ok(()) => true,
			Err(()) => {
				log::error!(
					target: LOG_TARGET,
					"Failed to submit registration transaction");
				false
			},
		}
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = AuthorityId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T> {
	type Key = AuthorityId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		assert!(
			NextAuthorityIds::<T>::iter().next().is_none(),
			"Initial authority IDs already set"
		);
		for (i, (_, authority_id)) in validators.enumerate() {
			NextAuthorityIds::<T>::insert(i as AuthorityIndex, authority_id);
		}
	}

	fn on_new_session<'a, I: 'a>(changed: bool, _validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, Self::Key)>,
	{
		let session_index = CurrentSessionIndex::<T>::mutate(|index| {
			*index += 1;
			*index
		});
		CurrentSessionStartBlock::<T>::put(frame_system::Pallet::<T>::block_number());

		// Discard the previous previous mixnode set, which we don't need any more
		check_removed_all(Mixnodes::<T>::clear_prefix(
			session_index.wrapping_sub(2),
			T::MaxAuthorities::get(),
			None,
		));

		if changed {
			// Save authority set for the next session. Note that we don't care about the authority
			// set for the current session; we just care about the key-exchange public keys that
			// were registered and are stored in Mixnodes.
			check_removed_all(NextAuthorityIds::<T>::clear(T::MaxAuthorities::get(), None));
			for (i, (_, authority_id)) in queued_validators.enumerate() {
				NextAuthorityIds::<T>::insert(i as AuthorityIndex, authority_id);
			}
		}
	}

	fn on_disabled(_i: u32) {
		// For now, to keep things simple, just ignore
		// TODO
	}
}
