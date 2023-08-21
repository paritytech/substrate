// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
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

use arrayref::array_mut_ref;
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
	*array_mut_ref![data, 0, 8] = block_number.to_le_bytes();
	*array_mut_ref![data, 8, KX_PUBLIC_SIZE] = *kx_public;
	u64::from_le_bytes(sp_io::hashing::twox_64(&data))
}

////////////////////////////////////////////////////////////////////////////////
// The pallet
////////////////////////////////////////////////////////////////////////////////

/// `$session_index` must be the index of the current session. If `$current` is `true`, evaluates
/// `$expr` with `$mixnodes<T>` aliased to the current mixnode set. Otherwise, evaluates `$expr`
/// with `$mixnodes<T>` aliased to the other mixnode set (which is either the next or previous
/// mixnode set, depending on the session phase).
macro_rules! with_mixnodes {
	($session_index:expr, $current:expr, $mixnodes:ident, $expr:expr) => {
		if (($session_index & 1) != 0) == $current {
			type $mixnodes<T> = OddSessionMixnodes<T>;
			$expr
		} else {
			type $mixnodes<T> = EvenSessionMixnodes<T>;
			$expr
		}
	};
}

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

		/// Length of the `CoverToCurrent` phase of each session, in blocks.
		#[pallet::constant]
		type NumCoverToCurrentBlocks: Get<BlockNumberFor<Self>>;

		/// Length of the `RequestsToCurrent` phase of each session, in blocks.
		#[pallet::constant]
		type NumRequestsToCurrentBlocks: Get<BlockNumberFor<Self>>;

		/// Length of the `CoverToPrev` phase of each session, in blocks.
		#[pallet::constant]
		type NumCoverToPrevBlocks: Get<BlockNumberFor<Self>>;

		/// The number of "slack" blocks at the start of the register phase (`DisconnectFromPrev`).
		/// [`maybe_register`](Pallet::maybe_register) will not attempt to post registration
		/// transactions during this slack period.
		#[pallet::constant]
		type NumRegisterStartSlackBlocks: Get<BlockNumberFor<Self>>;

		/// The number of "slack" blocks at the end of the register phase (`DisconnectFromPrev`).
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

	/// Mixnode set. Which mixnode set depends on the current session index and phase:
	///
	/// - Current session index is even (0, 2, ...): this is the current mixnode set.
	/// - Current session index is odd, before register phase (`DisconnectFromPrev`): this is the
	///   previous mixnode set.
	/// - Current session index is odd, register phase (`DisconnectFromPrev`): this is the next
	///   mixnode set.
	///
	/// The mixnodes are keyed by authority index so we can easily check if an authority has
	/// already registered a mixnode. The authority indices should only be used during
	/// registration; in the very first session the authority indices for the current mixnode set
	/// are made up.
	#[pallet::storage]
	pub(crate) type EvenSessionMixnodes<T> =
		StorageMap<_, Identity, AuthorityIndex, BoundedMixnodeFor<T>>;

	/// Mixnode set. Which mixnode set depends on the current session index and phase:
	///
	/// - Current session index is odd (1, 3, ...): this is the current mixnode set.
	/// - Current session index is even, before register phase (`DisconnectFromPrev`): this is the
	///   previous mixnode set.
	/// - Current session index is even, register phase (`DisconnectFromPrev`): this is the next
	///   mixnode set.
	///
	/// The mixnodes are keyed by authority index so we can easily check if an authority has
	/// already registered a mixnode. The authority indices should only be used during
	/// registration; in the very first session the authority indices for the previous mixnode set
	/// are made up.
	#[pallet::storage]
	pub(crate) type OddSessionMixnodes<T> =
		StorageMap<_, Identity, AuthorityIndex, BoundedMixnodeFor<T>>;

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
				EvenSessionMixnodes::<T>::iter().next().is_none(),
				"Initial mixnodes already set"
			);
			for (i, mixnode) in self.mixnodes.iter().enumerate() {
				// We just make up authority indices here. This doesn't matter as authority indices
				// are only used during registration to check an authority doesn't register twice.
				EvenSessionMixnodes::<T>::insert(i as AuthorityIndex, mixnode);
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
			debug_assert!(
				Self::session_phase(frame_system::Pallet::<T>::block_number()).0 ==
					SessionPhase::DisconnectFromPrev
			);
			debug_assert!(registration.authority_index < T::MaxAuthorities::get());

			with_mixnodes!(
				registration.session_index,
				false, // Registering for the _following_ session
				Mixnodes,
				Mixnodes::<T>::insert(registration.authority_index, registration.mixnode)
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

			// Check registrations are open
			let block_number = frame_system::Pallet::<T>::block_number();
			if Self::session_phase(block_number).0 != SessionPhase::DisconnectFromPrev {
				return InvalidTransaction::Future.into()
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

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(block_number: BlockNumberFor<T>) -> Weight {
			if Self::session_phase(block_number) == (SessionPhase::DisconnectFromPrev, Zero::zero())
			{
				// Right at the start of the register phase. Drop the previous mixnode set. From
				// this point forward, the storage will be used for the next mixnode set.
				Self::clear_prev_next_mixnodes();
			}
			Weight::zero() // TODO
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Returns the session phase and the number of blocks we have spent in this phase so far.
	fn session_phase(block_number: BlockNumberFor<T>) -> (SessionPhase, BlockNumberFor<T>) {
		let block_in_phase = block_number.saturating_sub(CurrentSessionStartBlock::<T>::get());
		let Some(block_in_phase) = block_in_phase.checked_sub(&T::NumCoverToCurrentBlocks::get())
		else {
			return (SessionPhase::CoverToCurrent, block_in_phase)
		};
		let Some(block_in_phase) =
			block_in_phase.checked_sub(&T::NumRequestsToCurrentBlocks::get())
		else {
			return (SessionPhase::RequestsToCurrent, block_in_phase)
		};
		let Some(block_in_phase) = block_in_phase.checked_sub(&T::NumCoverToPrevBlocks::get())
		else {
			return (SessionPhase::CoverToPrev, block_in_phase)
		};
		(SessionPhase::DisconnectFromPrev, block_in_phase)
	}

	/// Returns the index and phase of the current session.
	pub fn session_status() -> SessionStatus {
		SessionStatus {
			current_index: CurrentSessionIndex::<T>::get(),
			phase: Self::session_phase(frame_system::Pallet::<T>::block_number()).0,
		}
	}

	/// If `current` is `true`, returns the current mixnode set. Otherwise, returns the
	/// previous/next mixnode set (depending on the session phase).
	fn mixnodes(current: bool) -> Result<Vec<Mixnode>, MixnodesErr> {
		let mixnodes: Vec<_> = with_mixnodes!(
			CurrentSessionIndex::<T>::get(),
			current,
			Mixnodes,
			Mixnodes::<T>::iter_values()
		)
		.map(Into::into)
		.collect();
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
		if Self::session_phase(frame_system::Pallet::<T>::block_number()).0 ==
			SessionPhase::DisconnectFromPrev
		{
			// Non-current mixnodes are for next session now, not previous session
			Err(MixnodesErr::Discarded)
		} else {
			Self::mixnodes(false)
		}
	}

	/// Returns the mixnode set for the current session.
	pub fn current_mixnodes() -> Result<Vec<Mixnode>, MixnodesErr> {
		Self::mixnodes(true)
	}

	/// Clear the previous/next mixnode set (depending on the session phase).
	fn clear_prev_next_mixnodes() {
		with_mixnodes!(
			CurrentSessionIndex::<T>::get(),
			false, // Want to clear the previous/next mixnode set
			Mixnodes,
			check_removed_all(Mixnodes::<T>::clear(T::MaxAuthorities::get(), None))
		);
	}

	/// Is now a good time to register, considering only session progress?
	fn should_register_by_session_progress(
		block_number: BlockNumberFor<T>,
		mixnode: &Mixnode,
	) -> bool {
		let (phase, block_in_phase) = Self::session_phase(block_number);
		if (phase != SessionPhase::DisconnectFromPrev) ||
			(block_in_phase < T::NumRegisterStartSlackBlocks::get())
		{
			return false
		}

		let (Some(end_block), _weight) =
			T::NextSessionRotation::estimate_next_session_rotation(block_number)
		else {
			// Things aren't going to work terribly well in this case as all the authorities will
			// just pile in at the start of each register phase...
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

	/// `session_index` must be the index of the current session. `authority_index` is the
	/// authority index in the _next_ session. Should only be called during the register phase
	/// (`DisconnectFromPrev`).
	fn already_registered(session_index: SessionIndex, authority_index: AuthorityIndex) -> bool {
		with_mixnodes!(
			session_index,
			false, // Registration is for the _following_ session
			Mixnodes,
			Mixnodes::<T>::contains_key(authority_index)
		)
	}

	/// Try to register a mixnode for the next session. Returns `true` if a registration extrinsic
	/// is submitted. `session_index` should match `session_status().current_index`; if it does
	/// not, `false` is returned immediately. This should be called every block during the session,
	/// except, after `true` is returned, this should not be called for a few blocks, to give the
	/// submitted extrinsic a chance to get included.
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
		let block_number = frame_system::Pallet::<T>::block_number();

		// It is possible for the ending session to have never entered the register phase
		// (DisconnectFromPrev). Handle this case. Note that this should work whether
		// on_new_session() is called before or after our on_initialize() function; in the latter
		// case we may end up clearing the mixnode set twice, but this is harmless.
		let (phase, block_in_phase) = Self::session_phase(block_number);
		if (phase != SessionPhase::DisconnectFromPrev) || block_in_phase.is_zero() {
			Self::clear_prev_next_mixnodes();
		}

		CurrentSessionIndex::<T>::mutate(|index| *index += 1);
		CurrentSessionStartBlock::<T>::put(block_number);

		if changed {
			// Save authority set for the next session. Note that we don't care about the authority
			// set for the current session; we just care about the key-exchange public keys that
			// were registered and are stored in Odd/EvenSessionMixnodes.
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
