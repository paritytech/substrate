// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Encode, MaxEncodedLen};

use frame_support::{
	dispatch::{DispatchResultWithPostInfo, Pays},
	log,
	pallet_prelude::*,
	traits::{Get, KeyOwnerProofSystem, OneSessionHandler},
	weights::Weight,
	BoundedSlice, BoundedVec, Parameter,
};
use frame_system::{
	ensure_none, ensure_signed,
	pallet_prelude::{BlockNumberFor, OriginFor},
};
use sp_runtime::{
	generic::DigestItem,
	traits::{IsMember, Member},
	KeyTypeId, RuntimeAppPublic,
};
use sp_session::{GetSessionNumber, GetValidatorCount};
use sp_staking::SessionIndex;
use sp_std::prelude::*;

use beefy_primitives::{
	AuthorityIndex, BeefyAuthorityId, ConsensusLog, EquivocationProof, OnNewValidatorSet,
	ValidatorSet, BEEFY_ENGINE_ID, GENESIS_AUTHORITY_SET_ID,
};

mod default_weights;
mod equivocation;
#[cfg(test)]
mod mock;
#[cfg(test)]
mod tests;

pub use crate::equivocation::{
	BeefyEquivocationOffence, BeefyOffence, BeefyTimeSlot, EquivocationHandler, HandleEquivocation,
};
pub use pallet::*;

const LOG_TARGET: &str = "runtime::beefy";

#[frame_support::pallet]
pub mod pallet {
	use super::*;
	use frame_system::pallet_prelude::BlockNumberFor;

	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Authority identifier type
		type BeefyId: Member
			+ Parameter
			// todo: use custom signature hashing type
			+ BeefyAuthorityId<sp_runtime::traits::Keccak256>
			+ MaybeSerializeDeserialize
			+ MaxEncodedLen;

		/// A system for proving ownership of keys, i.e. that a given key was part
		/// of a validator set, needed for validating equivocation reports.
		type KeyOwnerProofSystem: KeyOwnerProofSystem<
			(KeyTypeId, Self::BeefyId),
			Proof = Self::KeyOwnerProof,
			IdentificationTuple = Self::KeyOwnerIdentification,
		>;

		/// The proof of key ownership, used for validating equivocation reports
		/// The proof must include the session index and validator count of the
		/// session at which the equivocation occurred.
		type KeyOwnerProof: Parameter + GetSessionNumber + GetValidatorCount;

		/// The identification of a key owner, used when reporting equivocations.
		type KeyOwnerIdentification: Parameter;

		/// The equivocation handling subsystem, defines methods to report an
		/// offence (after the equivocation has been validated) and for submitting a
		/// transaction to report an equivocation (from an offchain context).
		/// NOTE: when enabling equivocation handling (i.e. this type isn't set to
		/// `()`) you must use this pallet's `ValidateUnsigned` in the runtime
		/// definition.
		type HandleEquivocation: HandleEquivocation<Self>;

		/// The maximum number of authorities that can be added.
		type MaxAuthorities: Get<u32>;

		/// A hook to act on the new BEEFY validator set.
		///
		/// For some applications it might be beneficial to make the BEEFY validator set available
		/// externally apart from having it in the storage. For instance you might cache a light
		/// weight MMR root over validators and make it available for Light Clients.
		type OnNewValidatorSet: OnNewValidatorSet<<Self as Config>::BeefyId>;

		/// Weights for this pallet.
		type WeightInfo: WeightInfo;
	}

	#[pallet::pallet]
	pub struct Pallet<T>(PhantomData<T>);

	/// The current authorities set
	#[pallet::storage]
	#[pallet::getter(fn authorities)]
	pub(super) type Authorities<T: Config> =
		StorageValue<_, BoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	/// The current validator set id
	#[pallet::storage]
	#[pallet::getter(fn validator_set_id)]
	pub(super) type ValidatorSetId<T: Config> =
		StorageValue<_, beefy_primitives::ValidatorSetId, ValueQuery>;

	/// Authorities set scheduled to be used with the next session
	#[pallet::storage]
	#[pallet::getter(fn next_authorities)]
	pub(super) type NextAuthorities<T: Config> =
		StorageValue<_, BoundedVec<T::BeefyId, T::MaxAuthorities>, ValueQuery>;

	/// A mapping from BEEFY set ID to the index of the *most recent* session for which its
	/// members were responsible.
	///
	/// TWOX-NOTE: `ValidatorSetId` is not under user control.
	#[pallet::storage]
	#[pallet::getter(fn session_for_set)]
	pub(super) type SetIdSession<T: Config> =
		StorageMap<_, Twox64Concat, beefy_primitives::ValidatorSetId, SessionIndex>;

	/// Block number where BEEFY consensus is enabled/started.
	/// If changing this, make sure `Self::ValidatorSetId` is also reset to
	/// `GENESIS_AUTHORITY_SET_ID` in the state of the new block number configured here.
	#[pallet::storage]
	#[pallet::getter(fn genesis_block)]
	pub(super) type GenesisBlock<T: Config> =
		StorageValue<_, Option<BlockNumberFor<T>>, ValueQuery>;

	#[pallet::genesis_config]
	pub struct GenesisConfig<T: Config> {
		/// Initial set of BEEFY authorities.
		pub authorities: Vec<T::BeefyId>,
		/// Block number where BEEFY consensus should start.
		/// Should match the session where initial authorities are active.
		/// *Note:* Ideally use block number where GRANDPA authorities are changed,
		/// to guarantee the client gets a finality notification for exactly this block.
		pub genesis_block: Option<BlockNumberFor<T>>,
	}

	#[cfg(feature = "std")]
	impl<T: Config> Default for GenesisConfig<T> {
		fn default() -> Self {
			// BEEFY genesis will be first BEEFY-MANDATORY block,
			// use block number one instead of chain-genesis.
			let genesis_block = Some(sp_runtime::traits::One::one());
			Self { authorities: Vec::new(), genesis_block }
		}
	}

	#[pallet::genesis_build]
	impl<T: Config> GenesisBuild<T> for GenesisConfig<T> {
		fn build(&self) {
			Pallet::<T>::initialize(&self.authorities)
				// we panic here as runtime maintainers can simply reconfigure genesis and restart
				// the chain easily
				.expect("Authorities vec too big");
			<GenesisBlock<T>>::put(&self.genesis_block);
		}
	}

	#[pallet::error]
	pub enum Error<T> {
		/// A key ownership proof provided as part of an equivocation report is invalid.
		InvalidKeyOwnershipProof,
		/// An equivocation proof provided as part of an equivocation report is invalid.
		InvalidEquivocationProof,
		/// A given equivocation report is valid but already previously reported.
		DuplicateOffenceReport,
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Report voter equivocation/misbehavior. This method will verify the
		/// equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence
		/// will be reported.
		#[pallet::call_index(0)]
		#[pallet::weight(T::WeightInfo::report_equivocation(key_owner_proof.validator_count()))]
		pub fn report_equivocation(
			origin: OriginFor<T>,
			equivocation_proof: Box<
				EquivocationProof<
					BlockNumberFor<T>,
					T::BeefyId,
					<T::BeefyId as RuntimeAppPublic>::Signature,
				>,
			>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			let reporter = ensure_signed(origin)?;

			Self::do_report_equivocation(Some(reporter), *equivocation_proof, key_owner_proof)
		}

		/// Report voter equivocation/misbehavior. This method will verify the
		/// equivocation proof and validate the given key ownership proof
		/// against the extracted offender. If both are valid, the offence
		/// will be reported.
		///
		/// This extrinsic must be called unsigned and it is expected that only
		/// block authors will call it (validated in `ValidateUnsigned`), as such
		/// if the block author is defined it will be defined as the equivocation
		/// reporter.
		#[pallet::call_index(1)]
		#[pallet::weight(T::WeightInfo::report_equivocation(key_owner_proof.validator_count()))]
		pub fn report_equivocation_unsigned(
			origin: OriginFor<T>,
			equivocation_proof: Box<
				EquivocationProof<
					BlockNumberFor<T>,
					T::BeefyId,
					<T::BeefyId as RuntimeAppPublic>::Signature,
				>,
			>,
			key_owner_proof: T::KeyOwnerProof,
		) -> DispatchResultWithPostInfo {
			ensure_none(origin)?;

			Self::do_report_equivocation(
				T::HandleEquivocation::block_author(),
				*equivocation_proof,
				key_owner_proof,
			)
		}
	}

	#[pallet::validate_unsigned]
	impl<T: Config> ValidateUnsigned for Pallet<T> {
		type Call = Call<T>;
		fn pre_dispatch(call: &Self::Call) -> Result<(), TransactionValidityError> {
			Self::pre_dispatch(call)
		}
		fn validate_unsigned(source: TransactionSource, call: &Self::Call) -> TransactionValidity {
			Self::validate_unsigned(source, call)
		}
	}
}

impl<T: Config> Pallet<T> {
	/// Return the current active BEEFY validator set.
	pub fn validator_set() -> Option<ValidatorSet<T::BeefyId>> {
		let validators: BoundedVec<T::BeefyId, T::MaxAuthorities> = Self::authorities();
		let id: beefy_primitives::ValidatorSetId = Self::validator_set_id();
		ValidatorSet::<T::BeefyId>::new(validators, id)
	}

	/// Submits an extrinsic to report an equivocation. This method will create
	/// an unsigned extrinsic with a call to `report_equivocation_unsigned` and
	/// will push the transaction to the pool. Only useful in an offchain context.
	pub fn submit_unsigned_equivocation_report(
		equivocation_proof: EquivocationProof<
			BlockNumberFor<T>,
			T::BeefyId,
			<T::BeefyId as RuntimeAppPublic>::Signature,
		>,
		key_owner_proof: T::KeyOwnerProof,
	) -> Option<()> {
		T::HandleEquivocation::submit_unsigned_equivocation_report(
			equivocation_proof,
			key_owner_proof,
		)
		.ok()
	}

	fn change_authorities(
		new: BoundedVec<T::BeefyId, T::MaxAuthorities>,
		queued: BoundedVec<T::BeefyId, T::MaxAuthorities>,
	) {
		<Authorities<T>>::put(&new);

		let new_id = Self::validator_set_id() + 1u64;
		<ValidatorSetId<T>>::put(new_id);

		<NextAuthorities<T>>::put(&queued);

		if let Some(validator_set) = ValidatorSet::<T::BeefyId>::new(new, new_id) {
			let log = DigestItem::Consensus(
				BEEFY_ENGINE_ID,
				ConsensusLog::AuthoritiesChange(validator_set.clone()).encode(),
			);
			<frame_system::Pallet<T>>::deposit_log(log);

			let next_id = new_id + 1;
			if let Some(next_validator_set) = ValidatorSet::<T::BeefyId>::new(queued, next_id) {
				<T::OnNewValidatorSet as OnNewValidatorSet<_>>::on_new_validator_set(
					&validator_set,
					&next_validator_set,
				);
			}
		}
	}

	fn initialize(authorities: &Vec<T::BeefyId>) -> Result<(), ()> {
		if authorities.is_empty() {
			return Ok(())
		}

		if !<Authorities<T>>::get().is_empty() {
			return Err(())
		}

		let bounded_authorities =
			BoundedSlice::<T::BeefyId, T::MaxAuthorities>::try_from(authorities.as_slice())
				.map_err(|_| ())?;

		let id = GENESIS_AUTHORITY_SET_ID;
		<Authorities<T>>::put(bounded_authorities);
		<ValidatorSetId<T>>::put(id);
		// Like `pallet_session`, initialize the next validator set as well.
		<NextAuthorities<T>>::put(bounded_authorities);

		if let Some(validator_set) = ValidatorSet::<T::BeefyId>::new(authorities.clone(), id) {
			let next_id = id + 1;
			if let Some(next_validator_set) =
				ValidatorSet::<T::BeefyId>::new(authorities.clone(), next_id)
			{
				<T::OnNewValidatorSet as OnNewValidatorSet<_>>::on_new_validator_set(
					&validator_set,
					&next_validator_set,
				);
			}
		}

		// NOTE: initialize first session of first set. this is necessary for
		// the genesis set and session since we only update the set -> session
		// mapping whenever a new session starts, i.e. through `on_new_session`.
		SetIdSession::<T>::insert(0, 0);

		Ok(())
	}

	fn do_report_equivocation(
		reporter: Option<T::AccountId>,
		equivocation_proof: EquivocationProof<
			BlockNumberFor<T>,
			T::BeefyId,
			<T::BeefyId as RuntimeAppPublic>::Signature,
		>,
		key_owner_proof: T::KeyOwnerProof,
	) -> DispatchResultWithPostInfo {
		// We check the equivocation within the context of its set id (and
		// associated session) and round. We also need to know the validator
		// set count at the time of the offence since it is required to calculate
		// the slash amount.
		let set_id = equivocation_proof.set_id();
		let round = *equivocation_proof.round_number();
		let offender_id = equivocation_proof.offender_id().clone();
		let session_index = key_owner_proof.session();
		let validator_count = key_owner_proof.validator_count();

		// validate the key ownership proof extracting the id of the offender.
		let offender = T::KeyOwnerProofSystem::check_proof(
			(beefy_primitives::KEY_TYPE, offender_id),
			key_owner_proof,
		)
		.ok_or(Error::<T>::InvalidKeyOwnershipProof)?;

		// validate equivocation proof (check votes are different and signatures are valid).
		if !beefy_primitives::check_equivocation_proof(&equivocation_proof) {
			return Err(Error::<T>::InvalidEquivocationProof.into())
		}

		// check that the session id for the membership proof is within the
		// bounds of the set id reported in the equivocation.
		let set_id_session_index =
			Self::session_for_set(set_id).ok_or(Error::<T>::InvalidEquivocationProof)?;
		if session_index != set_id_session_index {
			return Err(Error::<T>::InvalidEquivocationProof.into())
		}

		// report to the offences module rewarding the sender.
		T::HandleEquivocation::report_offence(
			reporter.into_iter().collect(),
			<T::HandleEquivocation as HandleEquivocation<T>>::Offence::new(
				session_index,
				validator_count,
				offender,
				set_id,
				round,
			),
		)
		.map_err(|_| Error::<T>::DuplicateOffenceReport)?;

		// waive the fee since the report is valid and beneficial
		Ok(Pays::No.into())
	}
}

impl<T: Config> sp_runtime::BoundToRuntimeAppPublic for Pallet<T> {
	type Public = T::BeefyId;
}

impl<T: Config> OneSessionHandler<T::AccountId> for Pallet<T>
where
	T: pallet_session::Config,
{
	type Key = T::BeefyId;

	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::BeefyId)>,
	{
		let authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		// we panic here as runtime maintainers can simply reconfigure genesis and restart the
		// chain easily
		Self::initialize(&authorities).expect("Authorities vec too big");
	}

	fn on_new_session<'a, I: 'a>(_changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a T::AccountId, T::BeefyId)>,
	{
		let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
		if next_authorities.len() as u32 > T::MaxAuthorities::get() {
			log::error!(
				target: LOG_TARGET,
				"authorities list {:?} truncated to length {}",
				next_authorities,
				T::MaxAuthorities::get(),
			);
		}
		let bounded_next_authorities =
			BoundedVec::<_, T::MaxAuthorities>::truncate_from(next_authorities);

		let next_queued_authorities = queued_validators.map(|(_, k)| k).collect::<Vec<_>>();
		if next_queued_authorities.len() as u32 > T::MaxAuthorities::get() {
			log::error!(
				target: LOG_TARGET,
				"queued authorities list {:?} truncated to length {}",
				next_queued_authorities,
				T::MaxAuthorities::get(),
			);
		}
		let bounded_next_queued_authorities =
			BoundedVec::<_, T::MaxAuthorities>::truncate_from(next_queued_authorities);

		// Always issue a change on each `session`, even if validator set hasn't changed.
		// We want to have at least one BEEFY mandatory block per session.
		Self::change_authorities(bounded_next_authorities, bounded_next_queued_authorities);

		// Update the mapping for the new set id that corresponds to the latest session (i.e. now).
		let session_index = <pallet_session::Pallet<T>>::current_index();
		SetIdSession::<T>::insert(Self::validator_set_id(), &session_index);
	}

	fn on_disabled(i: u32) {
		let log = DigestItem::Consensus(
			BEEFY_ENGINE_ID,
			ConsensusLog::<T::BeefyId>::OnDisabled(i as AuthorityIndex).encode(),
		);

		<frame_system::Pallet<T>>::deposit_log(log);
	}
}

impl<T: Config> IsMember<T::BeefyId> for Pallet<T> {
	fn is_member(authority_id: &T::BeefyId) -> bool {
		Self::authorities().iter().any(|id| id == authority_id)
	}
}

pub trait WeightInfo {
	fn report_equivocation(validator_count: u32) -> Weight;
}
