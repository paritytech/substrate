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

//! GRANDPA Consensus module for runtime.
//!
//! This manages the GRANDPA authority set ready for the native code.
//! These authorities are only for GRANDPA finality, not for consensus overall.
//!
//! In the future, it will also handle misbehavior reports, and on-chain
//! finality notifications.
//!
//! For full integration with GRANDPA, the `GrandpaApi` should be implemented.
//! The necessary items are re-exported via the `fg_primitives` crate.

#![cfg_attr(not(feature = "std"), no_std)]

// re-export since this is necessary for `impl_apis` in runtime.
pub use substrate_finality_grandpa_primitives as fg_primitives;

use rstd::prelude::*;
use rstd::collections::{btree_map::BTreeMap, btree_set::BTreeSet};
use parity_codec::{self as codec, Encode, Decode, Codec};

use srml_support::{
	decl_event, decl_storage, decl_module, dispatch::Result, storage::StorageValue,
	Parameter, storage::StorageMap,
};
use primitives::{
	generic::{DigestItem, OpaqueDigestItemId, Block},
	traits::{
		CurrentHeight, MaybeSerializeDebug, ValidateUnsigned, Verify, Header as HeaderT,
		Block as BlockT, Member
	},
	transaction_validity::TransactionValidity
};
use fg_primitives::{
	ScheduledChange, GRANDPA_ENGINE_ID, GrandpaPrevote, GrandpaPrecommit,
	SignedPrecommit, VoterSet, GrandpaMessage, localized_payload, AncestryChain,
	Chain, validate_commit, ConsensusLog,
};
pub use fg_primitives::{
	AuthorityId, AuthorityWeight, AuthoritySignature, CHALLENGE_SESSION_LENGTH,
	Commit, safety::{self, ChallengedVote, RejectingVoteSet},
};

use session::historical::Proof;
use system::{DigestOf, ensure_signed};
use num_traits as num;
use core::iter::FromIterator;

mod mock;
mod tests;

type Hash<T> = <T as system::Trait>::Hash;
type Number<T> = <T as system::Trait>::BlockNumber;
type Header<T> = <T as system::Trait>::Header;

type StoredPendingChallenge<T> = safety::StoredPendingChallenge<Hash<T>, Number<T>, Header<T>>;
type StoredChallengeSession<T> = safety::StoredChallengeSession<Hash<T>, Number<T>, Header<T>>;

type Prevote<T> = GrandpaPrevote<Hash<T>, Number<T>>;
type Precommit<T> = GrandpaPrecommit<Hash<T>, Number<T>>;
type Message<T> = GrandpaMessage<Hash<T>, Number<T>>;

type Equivocation<T> = safety::GrandpaEquivocation<Hash<T>, Number<T>>;
type Challenge<T> = safety::Challenge<Hash<T>, Number<T>, Header<T>>;

pub trait Trait: system::Trait {
	/// The event type of this module.
	type Event: From<Event> + Into<<Self as system::Trait>::Event>;

	/// The signature of the authority.
	type Signature: Verify<Signer=AuthorityId> + Codec + Clone + Eq;

	/// The block.
	type Block: BlockT<Hash=<Self as system::Trait>::Hash, Header=<Self as system::Trait>::Header>;
}

/// A stored pending change, old format.
// TODO: remove shim
// https://github.com/paritytech/substrate/issues/1614
#[derive(Encode, Decode)]
pub struct OldStoredPendingChange<N> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(AuthorityId, u64)>,
}

/// A stored pending change.
#[derive(Encode)]
pub struct StoredPendingChange<N> {
	/// The block number this was scheduled at.
	pub scheduled_at: N,
	/// The delay in blocks until it will be applied.
	pub delay: N,
	/// The next authority set.
	pub next_authorities: Vec<(AuthorityId, u64)>,
	/// If defined it means the change was forced and the given block number
	/// indicates the median last finalized block when the change was signaled.
	pub forced: Option<N>,
}

impl<N: Decode> Decode for StoredPendingChange<N> {
	fn decode<I: codec::Input>(value: &mut I) -> Option<Self> {
		let old = OldStoredPendingChange::decode(value)?;
		let forced = <Option<N>>::decode(value).unwrap_or(None);

		Some(StoredPendingChange {
			scheduled_at: old.scheduled_at,
			delay: old.delay,
			next_authorities: old.next_authorities,
			forced,
		})
	}
}

decl_event!(
	pub enum Event {
		/// New authority set has been applied.
		NewAuthorities(Vec<(AuthorityId, u64)>),
		NewChallenge(Vec<AuthorityId>),
		ChallengeResponded(Vec<AuthorityId>),
	}
);

decl_storage! {
	trait Store for Module<T: Trait> as GrandpaFinality {
		/// The current authority set.
		Authorities get(authorities) config(): Vec<(AuthorityId, AuthorityWeight)>;

		/// Pending change: (signaled at, scheduled change).
		PendingChange: Option<StoredPendingChange<T::BlockNumber>>;

		/// Open challenge sessions.
		ChallengeSessions get(challenge_sessions): map T::Hash => Option<StoredChallengeSession<T>>;

		/// Pending challenges.
		PendingChallenges get(pending_challenges): Vec<StoredPendingChallenge<T>>;

		/// next block number where we can force a change.
		NextForced get(next_forced): Option<T::BlockNumber>;

		/// `true` if we are currently stalled.
		Stalled get(stalled): Option<(T::BlockNumber, T::BlockNumber)>;
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		fn deposit_event() = default;

		/// Report equivocation.
		fn report_equivocation(origin, proved_equivocation: (Equivocation<T>, Proof)) {
			ensure_signed(origin)?;

			let (equivocation, proof) = proved_equivocation;
			let identity = equivocation.identity;

			let first_vote = equivocation.first.0;
			let first_signature = equivocation.first.1;

			let second_vote = equivocation.second.0;
			let second_signature = equivocation.second.1;
			
			if first_vote != second_vote {
				let first_payload = localized_payload(
					equivocation.round_number,
					equivocation.set_id,
					&first_vote,
				);

				if !first_signature.verify(first_payload.as_slice(), &identity) {
					return Err("Bad signature")
				}

				let second_payload = localized_payload(
					equivocation.round_number,
					equivocation.set_id,
					&second_vote,
				);

				if !second_signature.verify(second_payload.as_slice(), &identity) {
					return Err("Bad signature")
				}

				// Slash identity
			}

			return Err("Votes are the same")
		}

		/// Answer a previous challenge by providing a set of prevotes.
		fn report_prevotes_answer(origin, answer: Challenge<T>) {
			ensure_signed(origin)?;

			// Check that prevotes set has supermajority for B.
			{
				let previous_challenge = <ChallengeSessions<T>>::take(answer.previous_challenge.expect("FIXME")).expect("FIXME");
				let challenge = previous_challenge.challenge;
				let headers: &[T::Header] = answer.rejecting_set.headers.as_slice();
				let votes = answer.rejecting_set.votes; // TODO: Check signatures.
				let commit = Commit::<_, _, Option<()>, _> {
					target_hash: challenge.finalized_block.0,
					target_number: challenge.finalized_block.1,
					precommits: votes.into_iter().map(|challenged_vote| {
						SignedPrecommit {
							precommit: Precommit::<T> {
								target_hash: *challenged_vote.vote.target().0,
								target_number: challenged_vote.vote.target().1,
							},
							signature: None, // TODO: Check it doesn't matter.
							id: challenged_vote.authority,
						}
					}).collect(),
				};

				let ancestry_chain = AncestryChain::<T::Block>::new(headers);
				let voters = <Module<T>>::grandpa_authorities();
				let voter_set = VoterSet::<AuthorityId>::from_iter(voters);

				if let Ok(validation_result) = validate_commit(&commit, &voter_set, &ancestry_chain) {
					if let Some(ghost) = validation_result.ghost() {
						// TODO: I think this should check that ghost is ancestor of B.
						if *ghost == answer.finalized_block {
							// TODO: get culprits
							// let culprits = get_culprits(previous_challenge.finalized_block_proof);
							// Slash culprits
						}
					}
				}
			}

			return Err("Invalid answer to challenge")
		}

		/// Report rejecting set of prevotes.
		fn report_rejecting_prevotes(origin, proved_challenge: (Challenge<T>, Vec<Proof>)) {
			ensure_signed(origin)?;

			let (challenge, proofs) = proved_challenge;

			let round_s = challenge.rejecting_set.round;
			let round_b = challenge.finalized_block_proof.round;

			if round_s == round_b {
				// Check that block proof contains supermajority of precommits for B.
				// TODO: Check signatures.
				{
					let headers: &[T::Header] = challenge.finalized_block_proof.headers.as_slice();
					let commit = challenge.finalized_block_proof.commit.clone();
					let ancestry_chain = AncestryChain::<T::Block>::new(headers);
					let voters = <Module<T>>::grandpa_authorities();
					let voter_set = VoterSet::<AuthorityId>::from_iter(voters);

					if let Ok(validation_result) = validate_commit(&commit, &voter_set, &ancestry_chain) {
						if let Some(ghost) = validation_result.ghost() {
							// TODO: I think this should check that ghost is ancestor of B.
							if *ghost != challenge.finalized_block {
								return Err("Invalid proof of finalized block")
							}
						}
					}
				}

				// Check that rejecting vote doesn't have supermajority for B.
				// TODO: check signatures.
				{
					let headers: &[T::Header] = challenge.rejecting_set.headers.as_slice();
					let votes = challenge.rejecting_set.votes.clone();
					let commit = Commit {
						target_hash: challenge.finalized_block.0,
						target_number: challenge.finalized_block.1,
						precommits: votes.into_iter().map(|challenged_vote| {
							SignedPrecommit {
								precommit: Precommit::<T> {
									target_hash: *challenged_vote.vote.target().0,
									target_number: challenged_vote.vote.target().1,
								},
								signature: challenged_vote.signature, // TODO: It doesn't matter
								id: challenged_vote.authority,
							}
						}).collect(),
					};
					let ancestry_chain = AncestryChain::<T::Block>::new(headers);
					let voters = <Module<T>>::grandpa_authorities();
					let voter_set = VoterSet::<AuthorityId>::from_iter(voters);

					if let Ok(validation_result) = validate_commit(&commit, &voter_set, &ancestry_chain) {
						if let Some(ghost) = validation_result.ghost() {
							// TODO: I think this should check that ghost is ancestor of B.
							if *ghost != challenge.finalized_block {
								return Err("Invalid proof of finalized block")
							}
						}
					}
				}
			} 
			
			if round_s > round_b {
				// Iterate by attaching a digest.

				// Push new session.
				let parent_hash = <system::Module<T>>::parent_hash();
				let current_height = <system::ChainContext::<T>>::default().current_height();

				let challenge_session = StoredPendingChallenge::<T> {
					scheduled_at: current_height,
					delay: CHALLENGE_SESSION_LENGTH.into(),
					parent_hash,
					challenge: challenge.clone(),
				};

				let mut pending_challenges = Self::pending_challenges();
				pending_challenges.push(challenge_session);
				<PendingChallenges<T>>::put(pending_challenges);
			}
		}

		/// Report rejecting set of precommits.
		fn report_rejecting_precommits(origin, proved_challenge: (Challenge<T>, Vec<Proof>)) {
			ensure_signed(origin)?;
			// TODO: Check that is a *new* challenge?
			
			let (challenge, proofs) = proved_challenge;

			// TODO: Check these two guys.
			let round_s = challenge.rejecting_set.round;
			let round_b = challenge.finalized_block_proof.round;

			if round_b == round_s {
				// Case 1: Rejecting set contains only precommits.
				let mut authority_vote_map = BTreeMap::new();
				let mut equivocators_set = BTreeSet::new();

				for challenged_vote in challenge.rejecting_set.votes.clone() {
					// TODO: Check signature.
					let ChallengedVote { vote, authority, signature } = challenged_vote;
					match authority_vote_map.get(&authority) {
						Some(previous_vote) => {
							if &vote != previous_vote {
								equivocators_set.insert(authority);
							}
						},
						None => {
							authority_vote_map.insert(authority, vote);
						},
					}
				}

				// TODO: Slash the equivocators in `equivocators_set`.
			}

			if round_s > round_b {
				// Iterate by attaching a digest.

				// Push new session.
				let parent_hash = <system::Module<T>>::parent_hash();
				let current_height = <system::ChainContext::<T>>::default().current_height();

				let challenge_session = StoredPendingChallenge::<T> {
					scheduled_at: current_height,
					delay: CHALLENGE_SESSION_LENGTH.into(),
					parent_hash,
					challenge: challenge.clone(),
				};

				let mut pending_challenges = Self::pending_challenges();
				pending_challenges.push(challenge_session);
				<PendingChallenges<T>>::put(pending_challenges);
			}
		}

		fn on_finalize(block_number: T::BlockNumber) {
			if let Some(pending_change) = <PendingChange<T>>::get() {
				if block_number == pending_change.scheduled_at {
					if let Some(median) = pending_change.forced {
						Self::deposit_log(ConsensusLog::ForcedChange(
							median,
							ScheduledChange{
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						))
					} else {
						Self::deposit_log(ConsensusLog::ScheduledChange(
							ScheduledChange{
								delay: pending_change.delay,
								next_authorities: pending_change.next_authorities.clone(),
							}
						));
					}
				}

				if block_number == pending_change.scheduled_at + pending_change.delay {
					Authorities::put(&pending_change.next_authorities);
					Self::deposit_event(
						Event::NewAuthorities(pending_change.next_authorities)
					);
					<PendingChange<T>>::kill();
				}
			}

			let pending_challenges = Self::pending_challenges();

			// if let Some(pending_challenge) = <PendingChallenge<T>>::get() {
				// Self::deposit_log(Signal::Challenge(Challenge { phantom_data: core::marker::PhantomData }))
			// }
		}
	}
}

impl<T: Trait> Module<T> {
	/// Get the current set of authorities, along with their respective weights.
	pub fn grandpa_authorities() -> Vec<(AuthorityId, u64)> {
		Authorities::get()
	}

	/// Schedule a change in the authorities.
	///
	/// The change will be applied at the end of execution of the block
	/// `in_blocks` after the current block. This value may be 0, in which
	/// case the change is applied at the end of the current block.
	///
	/// If the `forced` parameter is defined, this indicates that the current
	/// set has been synchronously determined to be offline and that after
	/// `in_blocks` the given change should be applied. The given block number
	/// indicates the median last finalized block number and it should be used
	/// as the canon block when starting the new grandpa voter.
	///
	/// No change should be signaled while any change is pending. Returns
	/// an error if a change is already pending.
	pub fn schedule_change(
		next_authorities: Vec<(AuthorityId, u64)>,
		in_blocks: T::BlockNumber,
		forced: Option<T::BlockNumber>,
	) -> Result {
		if !<PendingChange<T>>::exists() {
			let scheduled_at = system::ChainContext::<T>::default().current_height();

			if let Some(_) = forced {
				if Self::next_forced().map_or(false, |next| next > scheduled_at) {
					return Err("Cannot signal forced change so soon after last.");
				}

				// only allow the next forced change when twice the window has passed since
				// this one.
				<NextForced<T>>::put(scheduled_at + in_blocks * 2.into());
			}

			<PendingChange<T>>::put(StoredPendingChange {
				delay: in_blocks,
				scheduled_at,
				next_authorities,
				forced,
			});

			Ok(())
		} else {
			Err("Attempt to signal GRANDPA change with one already pending.")
		}
	}

	/// Deposit one of this module's logs.
	fn deposit_log(log: ConsensusLog<T::Hash, T::BlockNumber, T::Header>) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(GRANDPA_ENGINE_ID, log.encode());
		<system::Module<T>>::deposit_log(log.into());
	}
}

impl<T: Trait> Module<T> {
	pub fn grandpa_log(digest: &DigestOf<T>) -> Option<ConsensusLog<T::Hash, T::BlockNumber, T::Header>> {
		let id = OpaqueDigestItemId::Consensus(&GRANDPA_ENGINE_ID);
		digest.convert_first(|l| l.try_to::<ConsensusLog<T::Hash, T::BlockNumber, T::Header>>(id))
	}

	pub fn pending_change(digest: &DigestOf<T>)
		-> Option<ScheduledChange<T::BlockNumber>>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_change())
	}

	pub fn forced_change(digest: &DigestOf<T>)
		-> Option<(T::BlockNumber, ScheduledChange<T::BlockNumber>)>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_forced_change())
	}

	pub fn grandpa_challenges(digest: &DigestOf<T>) -> Option<Vec<Challenge<T>>>
	{
		Self::grandpa_log(digest).and_then(|signal| signal.try_into_challenges())
	}
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = AuthorityId;

	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| (k, 1u64)).collect::<Vec<_>>();
			let last_authorities = <Module<T>>::grandpa_authorities();
			if next_authorities != last_authorities {
				use primitives::traits::Zero;
				if let Some((further_wait, median)) = <Stalled<T>>::take() {
					let _ = Self::schedule_change(next_authorities, further_wait, Some(median));
				} else {
					let _ = Self::schedule_change(next_authorities, Zero::zero(), None);
				}
			}
		}
	}
	fn on_disabled(i: usize) {
		Self::deposit_log(ConsensusLog::OnDisabled(i as u64))
	}
}

impl<T: Trait> finality_tracker::OnFinalizationStalled<T::BlockNumber> for Module<T> {
	fn on_stalled(further_wait: T::BlockNumber, median: T::BlockNumber) {
		// when we record old authority sets, we can use `finality_tracker::median`
		// to figure out _who_ failed. until then, we can't meaningfully guard
		// against `next == last` the way that normal session changes do.
		<Stalled<T>>::put((further_wait, median));
	}
}

