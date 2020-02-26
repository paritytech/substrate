// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

//! Primitives for GRANDPA integration, suitable for WASM compilation.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(not(feature = "std"))]
extern crate alloc;

#[cfg(feature = "std")]
use serde::Serialize;

use codec::{Encode, Decode, Input, Codec};
use sp_runtime::{ConsensusEngineId, RuntimeDebug, traits::NumberFor};
use sp_std::borrow::Cow;
use sp_std::vec::Vec;

#[cfg(feature = "std")]
use log::debug;

pub use sp_application_crypto::key_types::GRANDPA;

mod app {
	use sp_application_crypto::{app_crypto, key_types::GRANDPA, ed25519};
	app_crypto!(ed25519, GRANDPA);
}

sp_application_crypto::with_pair! {
	/// The grandpa crypto scheme defined via the keypair type.
	pub type AuthorityPair = app::Pair;
}

/// Identity of a Grandpa authority.
pub type AuthorityId = app::Public;

/// Signature for a Grandpa authority.
pub type AuthoritySignature = app::Signature;

/// The `ConsensusEngineId` of GRANDPA.
pub const GRANDPA_ENGINE_ID: ConsensusEngineId = *b"FRNK";

/// The storage key for the current set of weighted Grandpa authorities.
/// The value stored is an encoded VersionedAuthorityList.
pub const GRANDPA_AUTHORITIES_KEY: &'static [u8] = b":grandpa_authorities";

/// The weight of an authority.
pub type AuthorityWeight = u64;

/// The index of an authority.
pub type AuthorityIndex = u64;

/// The monotonic identifier of a GRANDPA set of authorities.
pub type SetId = u64;

/// The round indicator.
pub type RoundNumber = u64;

/// A list of Grandpa authorities with associated weights.
pub type AuthorityList = Vec<(AuthorityId, AuthorityWeight)>;

/// A scheduled change of authority set.
#[cfg_attr(feature = "std", derive(Serialize))]
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub struct ScheduledChange<N> {
	/// The new authorities after the change, along with their respective weights.
	pub next_authorities: AuthorityList,
	/// The number of blocks to delay.
	pub delay: N,
}

/// An consensus log item for GRANDPA.
#[cfg_attr(feature = "std", derive(Serialize))]
#[derive(Decode, Encode, PartialEq, Eq, Clone, RuntimeDebug)]
pub enum ConsensusLog<N: Codec> {
	/// Schedule an authority set change.
	///
	/// The earliest digest of this type in a single block will be respected,
	/// provided that there is no `ForcedChange` digest. If there is, then the
	/// `ForcedChange` will take precedence.
	///
	/// No change should be scheduled if one is already and the delay has not
	/// passed completely.
	///
	/// This should be a pure function: i.e. as long as the runtime can interpret
	/// the digest type it should return the same result regardless of the current
	/// state.
	#[codec(index = "1")]
	ScheduledChange(ScheduledChange<N>),
	/// Force an authority set change.
	///
	/// Forced changes are applied after a delay of _imported_ blocks,
	/// while pending changes are applied after a delay of _finalized_ blocks.
	///
	/// The earliest digest of this type in a single block will be respected,
	/// with others ignored.
	///
	/// No change should be scheduled if one is already and the delay has not
	/// passed completely.
	///
	/// This should be a pure function: i.e. as long as the runtime can interpret
	/// the digest type it should return the same result regardless of the current
	/// state.
	#[codec(index = "2")]
	ForcedChange(N, ScheduledChange<N>),
	/// Note that the authority with given index is disabled until the next change.
	#[codec(index = "3")]
	OnDisabled(AuthorityIndex),
	/// A signal to pause the current authority set after the given delay.
	/// After finalizing the block at _delay_ the authorities should stop voting.
	#[codec(index = "4")]
	Pause(N),
	/// A signal to resume the current authority set after the given delay.
	/// After authoring the block at _delay_ the authorities should resume voting.
	#[codec(index = "5")]
	Resume(N),
}

impl<N: Codec> ConsensusLog<N> {
	/// Try to cast the log entry as a contained signal.
	pub fn try_into_change(self) -> Option<ScheduledChange<N>> {
		match self {
			ConsensusLog::ScheduledChange(change) => Some(change),
			_ => None,
		}
	}

	/// Try to cast the log entry as a contained forced signal.
	pub fn try_into_forced_change(self) -> Option<(N, ScheduledChange<N>)> {
		match self {
			ConsensusLog::ForcedChange(median, change) => Some((median, change)),
			_ => None,
		}
	}

	/// Try to cast the log entry as a contained pause signal.
	pub fn try_into_pause(self) -> Option<N> {
		match self {
			ConsensusLog::Pause(delay) => Some(delay),
			_ => None,
		}
	}

	/// Try to cast the log entry as a contained resume signal.
	pub fn try_into_resume(self) -> Option<N> {
		match self {
			ConsensusLog::Resume(delay) => Some(delay),
			_ => None,
		}
	}
}

#[derive(Clone, Debug, Decode, Encode, PartialEq)]
pub struct EquivocationProof<H, N> {
	set_id: SetId,
	equivocation: Equivocation<H, N>,
}

impl<H, N> EquivocationProof<H, N> {
	pub fn new(set_id: SetId, equivocation: Equivocation<H, N>) -> Self {
		EquivocationProof {
			set_id,
			equivocation,
		}
	}

	pub fn set_id(&self) -> SetId {
		self.set_id
	}

	pub fn round(&self) -> RoundNumber {
		match self.equivocation {
			Equivocation::Prevote(ref equivocation) => equivocation.round_number,
			Equivocation::Precommit(ref equivocation) => equivocation.round_number,
		}
	}

	pub fn offender(&self) -> &AuthorityId {
		self.equivocation.offender()
	}
}

#[derive(Clone, Debug, Decode, Encode, PartialEq)]
pub enum Equivocation<H, N> {
	Prevote(
		grandpa::Equivocation<
			AuthorityId,
			grandpa::Prevote<H, N>,
			AuthoritySignature,
		>,
	),
	Precommit(
		grandpa::Equivocation<
			AuthorityId,
			grandpa::Precommit<H, N>,
			AuthoritySignature,
		>,
	),
}

impl<H, N> From<grandpa::Equivocation<AuthorityId, grandpa::Prevote<H, N>, AuthoritySignature>>
	for Equivocation<H, N>
{
	fn from(
		equivocation: grandpa::Equivocation<
			AuthorityId,
			grandpa::Prevote<H, N>,
			AuthoritySignature,
		>,
	) -> Self {
		Equivocation::Prevote(equivocation)
	}
}

impl<H, N> From<grandpa::Equivocation<AuthorityId, grandpa::Precommit<H, N>, AuthoritySignature>>
	for Equivocation<H, N>
{
	fn from(
		equivocation: grandpa::Equivocation<
			AuthorityId,
			grandpa::Precommit<H, N>,
			AuthoritySignature,
		>,
	) -> Self {
		Equivocation::Precommit(equivocation)
	}
}

impl<H, N> Equivocation<H, N> {
	pub fn offender(&self) -> &AuthorityId {
		match self {
			Equivocation::Prevote(ref equivocation) => &equivocation.identity,
			Equivocation::Precommit(ref equivocation) => &equivocation.identity,
		}
	}
}

pub fn check_equivocation_proof<H, N>(report: &EquivocationProof<H, N>) -> Result<(), ()>
where
	H: Clone + Encode + PartialEq,
	N: Clone + Encode + PartialEq,
{
	// NOTE: the bare `Prevote` and `Precommit` types don't share any trait,
	// this is implemented as a macro to avoid duplication.
	macro_rules! check {
		( $equivocation:expr, $message:expr ) => {
			// if both votes have the same target the equivocation is invalid.
			if $equivocation.first.0.target_hash == $equivocation.second.0.target_hash &&
				$equivocation.first.0.target_number == $equivocation.second.0.target_number {
				return Err(());
			}

			// check signatures on both votes are valid
			check_message_signature(
				&$message($equivocation.first.0.clone()),
				&$equivocation.identity,
				&$equivocation.first.1,
				$equivocation.round_number,
				report.set_id,
			)?;

			check_message_signature(
				&$message($equivocation.second.0.clone()),
				&$equivocation.identity,
				&$equivocation.second.1,
				$equivocation.round_number,
				report.set_id,
			)?;

			return Ok(());
		}
	}

	match report.equivocation {
		Equivocation::Prevote(ref equivocation) => {
			check!(equivocation, grandpa::Message::Prevote);
		},
		Equivocation::Precommit(ref equivocation) => {
			check!(equivocation, grandpa::Message::Precommit);
		},
	}
}

/// Encode round message localized to a given round and set id.
pub fn localized_payload<E: Encode>(
	round: RoundNumber,
	set_id: SetId,
	message: &E,
) -> Vec<u8> {
	let mut buf = Vec::new();
	localized_payload_with_buffer(round, set_id, message, &mut buf);
	buf
}

/// Encode round message localized to a given round and set id using the given
/// buffer. The given buffer will be cleared and the resulting encoded payload
/// will always be written to the start of the buffer.
pub fn localized_payload_with_buffer<E: Encode>(
	round: RoundNumber,
	set_id: SetId,
	message: &E,
	buf: &mut Vec<u8>,
) {
	buf.clear();
	(message, round, set_id).encode_to(buf)
}

/// Check a message signature by encoding the message as a localized payload and
/// verifying the provided signature using the expected authority id.
pub fn check_message_signature<H, N>(
	message: &grandpa::Message<H, N>,
	id: &AuthorityId,
	signature: &AuthoritySignature,
	round: RoundNumber,
	set_id: SetId,
) -> Result<(), ()> where
	H: Encode,
	N: Encode,
{
	check_message_signature_with_buffer(
		message,
		id,
		signature,
		round,
		set_id,
		&mut Vec::new(),
	)
}

/// Check a message signature by encoding the message as a localized payload and
/// verifying the provided signature using the expected authority id.
/// The encoding necessary to verify the signature will be done using the given
/// buffer, the original content of the buffer will be cleared.
pub fn check_message_signature_with_buffer<H, N>(
	message: &grandpa::Message<H, N>,
	id: &AuthorityId,
	signature: &AuthoritySignature,
	round: RoundNumber,
	set_id: SetId,
	buf: &mut Vec<u8>,
) -> Result<(), ()> where
	H: Encode,
	N: Encode,
{
	localized_payload_with_buffer(round, set_id, message, buf);

	#[cfg(not(feature = "std"))]
	let verify = || {
		use sp_application_crypto::RuntimeAppPublic;
		id.verify(&buf, signature)
	};

	#[cfg(feature = "std")]
	let verify = || {
		use sp_application_crypto::Pair;
		AuthorityPair::verify(signature, &buf, &id)
	};

	if verify() {
		Ok(())
	} else {
		#[cfg(feature = "std")]
		debug!(target: "afg", "Bad signature on message from {:?}", id);

		Err(())
	}
}

#[cfg(feature = "std")]
pub fn sign_message<H, N>(
	message: grandpa::Message<H, N>,
	pair: &AuthorityPair,
	round: RoundNumber,
	set_id: SetId,
) -> grandpa::SignedMessage<H, N, AuthoritySignature, AuthorityId> where
	H: Encode,
	N: Encode,
{
	use sp_core::Pair;

	let encoded = localized_payload(round, set_id, &message);
	let signature = pair.sign(&encoded[..]);

	grandpa::SignedMessage {
		message,
		signature,
		id: pair.public(),
	}
}

/// WASM function call to check for pending changes.
pub const PENDING_CHANGE_CALL: &str = "grandpa_pending_change";
/// WASM function call to get current GRANDPA authorities.
pub const AUTHORITIES_CALL: &str = "grandpa_authorities";

/// The current version of the stored AuthorityList type. The encoding version MUST be updated any
/// time the AuthorityList type changes.
const AUTHORITIES_VERSION: u8 = 1;

/// An AuthorityList that is encoded with a version specifier. The encoding version is updated any
/// time the AuthorityList type changes. This ensures that encodings of different versions of an
/// AuthorityList are differentiable. Attempting to decode an authority list with an unknown
/// version will fail.
#[derive(Default)]
pub struct VersionedAuthorityList<'a>(Cow<'a, AuthorityList>);

impl<'a> From<AuthorityList> for VersionedAuthorityList<'a> {
	fn from(authorities: AuthorityList) -> Self {
		VersionedAuthorityList(Cow::Owned(authorities))
	}
}

impl<'a> From<&'a AuthorityList> for VersionedAuthorityList<'a> {
	fn from(authorities: &'a AuthorityList) -> Self {
		VersionedAuthorityList(Cow::Borrowed(authorities))
	}
}

impl<'a> Into<AuthorityList> for VersionedAuthorityList<'a> {
	fn into(self) -> AuthorityList {
		self.0.into_owned()
	}
}

impl<'a> Encode for VersionedAuthorityList<'a> {
	fn size_hint(&self) -> usize {
		(AUTHORITIES_VERSION, self.0.as_ref()).size_hint()
	}

	fn using_encoded<R, F: FnOnce(&[u8]) -> R>(&self, f: F) -> R {
		(AUTHORITIES_VERSION, self.0.as_ref()).using_encoded(f)
	}
}

impl<'a> Decode for VersionedAuthorityList<'a> {
	fn decode<I: Input>(value: &mut I) -> Result<Self, codec::Error> {
		let (version, authorities): (u8, AuthorityList) = Decode::decode(value)?;
		if version != AUTHORITIES_VERSION {
			return Err("unknown Grandpa authorities version".into());
		}
		Ok(authorities.into())
	}
}

sp_api::decl_runtime_apis! {
	/// APIs for integrating the GRANDPA finality gadget into runtimes.
	/// This should be implemented on the runtime side.
	///
	/// This is primarily used for negotiating authority-set changes for the
	/// gadget. GRANDPA uses a signaling model of changing authority sets:
	/// changes should be signaled with a delay of N blocks, and then automatically
	/// applied in the runtime after those N blocks have passed.
	///
	/// The consensus protocol will coordinate the handoff externally.
	#[api_version(2)]
	pub trait GrandpaApi {
		/// Get the current GRANDPA authorities and weights. This should not change except
		/// for when changes are scheduled and the corresponding delay has passed.
		///
		/// When called at block B, it will return the set of authorities that should be
		/// used to finalize descendants of this block (B+1, B+2, ...). The block B itself
		/// is finalized by the authorities from block B-1.
		fn grandpa_authorities() -> AuthorityList;

		#[skip_initialize_block]
		fn submit_report_equivocation_extrinsic(
			equivocation_proof: EquivocationProof<Block::Hash, NumberFor<Block>>,
			key_owner_proof: Vec<u8>,
		) -> Option<()>;
	}
}
