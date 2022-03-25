// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Traits for dealing with validation and validators.

use crate::{dispatch::Parameter, weights::Weight};
use codec::{Codec, Decode, MaxEncodedLen};
use sp_runtime::{
	traits::{Convert, Zero},
	BoundToRuntimeAppPublic, ConsensusEngineId, Permill, RuntimeAppPublic,
};
use sp_staking::SessionIndex;
use sp_std::prelude::*;

/// A trait for online node inspection in a session.
///
/// Something that can give information about the current validator set.
pub trait ValidatorSet<AccountId> {
	/// Type for representing validator id in a session.
	type ValidatorId: Parameter + MaxEncodedLen;
	/// A type for converting `AccountId` to `ValidatorId`.
	type ValidatorIdOf: Convert<AccountId, Option<Self::ValidatorId>>;

	/// Returns current session index.
	fn session_index() -> SessionIndex;

	/// Returns the active set of validators.
	fn validators() -> Vec<Self::ValidatorId>;
}

/// [`ValidatorSet`] combined with an identification.
pub trait ValidatorSetWithIdentification<AccountId>: ValidatorSet<AccountId> {
	/// Full identification of `ValidatorId`.
	type Identification: Parameter;
	/// A type for converting `ValidatorId` to `Identification`.
	type IdentificationOf: Convert<Self::ValidatorId, Option<Self::Identification>>;
}

/// A trait for finding the author of a block header based on the `PreRuntime` digests contained
/// within it.
pub trait FindAuthor<Author> {
	/// Find the author of a block based on the pre-runtime digests.
	fn find_author<'a, I>(digests: I) -> Option<Author>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>;
}

impl<A> FindAuthor<A> for () {
	fn find_author<'a, I>(_: I) -> Option<A>
	where
		I: 'a + IntoIterator<Item = (ConsensusEngineId, &'a [u8])>,
	{
		None
	}
}

/// A trait for verifying the seal of a header and returning the author.
pub trait VerifySeal<Header, Author> {
	/// Verify a header and return the author, if any.
	fn verify_seal(header: &Header) -> Result<Option<Author>, &'static str>;
}

/// A session handler for specific key type.
pub trait OneSessionHandler<ValidatorId>: BoundToRuntimeAppPublic {
	/// The key type expected.
	type Key: Decode + RuntimeAppPublic;

	/// The given validator set will be used for the genesis session.
	/// It is guaranteed that the given validator set will also be used
	/// for the second session, therefore the first call to `on_new_session`
	/// should provide the same validator set.
	fn on_genesis_session<'a, I: 'a>(validators: I)
	where
		I: Iterator<Item = (&'a ValidatorId, Self::Key)>,
		ValidatorId: 'a;

	/// Session set has changed; act appropriately. Note that this can be called
	/// before initialization of your module.
	///
	/// `changed` is true when at least one of the session keys
	/// or the underlying economic identities/distribution behind one the
	/// session keys has changed, false otherwise.
	///
	/// The `validators` are the validators of the incoming session, and `queued_validators`
	/// will follow.
	fn on_new_session<'a, I: 'a>(changed: bool, validators: I, queued_validators: I)
	where
		I: Iterator<Item = (&'a ValidatorId, Self::Key)>,
		ValidatorId: 'a;

	/// A notification for end of the session.
	///
	/// Note it is triggered before any `SessionManager::end_session` handlers,
	/// so we can still affect the validator set.
	fn on_before_session_ending() {}

	/// A validator got disabled. Act accordingly until a new session begins.
	fn on_disabled(_validator_index: u32);
}

/// Something that can estimate at which block the next session rotation will happen (i.e. a new
/// session starts).
///
/// The accuracy of the estimates is dependent on the specific implementation, but in order to get
/// the best estimate possible these methods should be called throughout the duration of the session
/// (rather than calling once and storing the result).
///
/// This should be the same logical unit that dictates `ShouldEndSession` to the session module. No
/// assumptions are made about the scheduling of the sessions.
pub trait EstimateNextSessionRotation<BlockNumber> {
	/// Return the average length of a session.
	///
	/// This may or may not be accurate.
	fn average_session_length() -> BlockNumber;

	/// Return an estimate of the current session progress.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_current_session_progress(now: BlockNumber) -> (Option<Permill>, Weight);

	/// Return the block number at which the next session rotation is estimated to happen.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_next_session_rotation(now: BlockNumber) -> (Option<BlockNumber>, Weight);
}

impl<BlockNumber: Zero> EstimateNextSessionRotation<BlockNumber> for () {
	fn average_session_length() -> BlockNumber {
		Zero::zero()
	}

	fn estimate_current_session_progress(_: BlockNumber) -> (Option<Permill>, Weight) {
		(None, Zero::zero())
	}

	fn estimate_next_session_rotation(_: BlockNumber) -> (Option<BlockNumber>, Weight) {
		(None, Zero::zero())
	}
}

/// Something that can estimate at which block scheduling of the next session will happen (i.e when
/// we will try to fetch new validators).
///
/// This only refers to the point when we fetch the next session details and not when we enact them
/// (for enactment there's `EstimateNextSessionRotation`). With `pallet-session` this should be
/// triggered whenever `SessionManager::new_session` is called.
///
/// For example, if we are using a staking module this would be the block when the session module
/// would ask staking what the next validator set will be, as such this must always be implemented
/// by the session module.
pub trait EstimateNextNewSession<BlockNumber> {
	/// Return the average length of a session.
	///
	/// This may or may not be accurate.
	fn average_session_length() -> BlockNumber;

	/// Return the block number at which the next new session is estimated to happen.
	///
	/// None should be returned if the estimation fails to come to an answer.
	fn estimate_next_new_session(_: BlockNumber) -> (Option<BlockNumber>, Weight);
}

impl<BlockNumber: Zero> EstimateNextNewSession<BlockNumber> for () {
	fn average_session_length() -> BlockNumber {
		Zero::zero()
	}

	fn estimate_next_new_session(_: BlockNumber) -> (Option<BlockNumber>, Weight) {
		(None, Zero::zero())
	}
}

/// Something which can compute and check proofs of
/// a historical key owner and return full identification data of that
/// key owner.
pub trait KeyOwnerProofSystem<Key> {
	/// The proof of membership itself.
	type Proof: Codec;
	/// The full identification of a key owner and the stash account.
	type IdentificationTuple: Codec;

	/// Prove membership of a key owner in the current block-state.
	///
	/// This should typically only be called off-chain, since it may be
	/// computationally heavy.
	///
	/// Returns `Some` iff the key owner referred to by the given `key` is a
	/// member of the current set.
	fn prove(key: Key) -> Option<Self::Proof>;

	/// Check a proof of membership on-chain. Return `Some` iff the proof is
	/// valid and recent enough to check.
	fn check_proof(key: Key, proof: Self::Proof) -> Option<Self::IdentificationTuple>;
}

impl<Key> KeyOwnerProofSystem<Key> for () {
	// The proof and identification tuples is any bottom type to guarantee that the methods of this
	// implementation can never be called or return anything other than `None`.
	type Proof = crate::Void;
	type IdentificationTuple = crate::Void;

	fn prove(_key: Key) -> Option<Self::Proof> {
		None
	}

	fn check_proof(_key: Key, _proof: Self::Proof) -> Option<Self::IdentificationTuple> {
		None
	}
}

/// Trait to be used by block producing consensus engine modules to determine
/// how late the current block is (e.g. in a slot-based proposal mechanism how
/// many slots were skipped since the previous block).
pub trait Lateness<N> {
	/// Returns a generic measure of how late the current block is compared to
	/// its parent.
	fn lateness(&self) -> N;
}

impl<N: Zero> Lateness<N> for () {
	fn lateness(&self) -> N {
		Zero::zero()
	}
}

/// Implementors of this trait provide information about whether or not some validator has
/// been registered with them. The [Session module](../../pallet_session/index.html) is an
/// implementor.
pub trait ValidatorRegistration<ValidatorId> {
	/// Returns true if the provided validator ID has been registered with the implementing runtime
	/// module
	fn is_registered(id: &ValidatorId) -> bool;
}

/// Trait used to check whether a given validator is currently disabled and should not be
/// participating in consensus (e.g. because they equivocated).
pub trait DisabledValidators {
	/// Returns true if the given validator is disabled.
	fn is_disabled(index: u32) -> bool;
}

impl DisabledValidators for () {
	fn is_disabled(_index: u32) -> bool {
		false
	}
}
