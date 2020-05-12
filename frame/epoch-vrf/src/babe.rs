use sp_std::{prelude::*, marker::PhantomData};
use codec::{Encode, Decode};
use frame_support::{ConsensusEngineId, traits::{Get, FindAuthor}};
use sp_runtime::generic::DigestItem;
use sp_consensus_babe::{SlotNumber, AuthorityId, BabeAuthorityWeight, ConsensusLog, BABE_ENGINE_ID};
use sp_consensus_babe::digests::{RawPreDigest, NextEpochDescriptor};
use sp_consensus_epoch_vrf::schnorrkel;
use crate::{EpochChangeTrigger, Trait, RawPreDigest as RawPreDigestT};

pub trait BabeTrait: pallet_timestamp::Trait {
	/// The amount of time, in slots, that each epoch should last.
	type EpochDuration: Get<SlotNumber>;

	/// The expected average block time at which BABE should be creating
	/// blocks. Since BABE is probabilistic it is not trivial to figure out
	/// what the expected average block time should be based on the slot
	/// duration and the security parameter `c` (where `1 - c` represents
	/// the probability of a slot being empty).
	type ExpectedBlockTime: Get<Self::Moment>;

	/// BABE requires some logic to be triggered on every block to query for whether an epoch
	/// has ended and to perform the transition to the next epoch.
	///
	/// Typically, the `ExternalTrigger` type should be used. An internal trigger should only be used
	/// when no other module is responsible for changing authority set.
	type EpochChangeTrigger: EpochChangeTrigger;
}

impl<T: BabeTrait> Trait for T {
	type EpochDuration = <T as BabeTrait>::EpochDuration;
	type ExpectedBlockTime = <T as BabeTrait>::ExpectedBlockTime;
	type EpochChangeTrigger = <T as BabeTrait>::EpochChangeTrigger;

	type AuthorityId = AuthorityId;
	type AuthorityWeight = BabeAuthorityWeight;
	type SlotNumber = SlotNumber;
	type RawPreDigest = RawPreDigest;

	fn find_raw_pre_digest() -> Option<Self::RawPreDigest> {
		<frame_system::Module<T>>::digest()
			.logs
			.iter()
			.filter_map(|s| s.as_pre_runtime())
			.filter_map(|(id, mut data)| if id == BABE_ENGINE_ID {
				PreDigest::decode(&mut data).ok()
			} else {
				None
			})
			.next()
	}

	fn deposit_next_epoch_descriptor(
		next_authorities: Vec<(Self::AuthorityId, Self::AuthorityWeight)>,
		next_randomness: schnorrkel::Randomness,
	) {
		let next = NextEpochDescriptor {
			authorities: next_authorities,
			randomness: next_randomness,
		};

		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			BABE_ENGINE_ID,
			ConsensusLog::NextEpochData(next).encode()
		);
		<frame_system::Module<T>>::deposit_log(log.into());
	}

	fn deposit_disabled_event(i: u32) {
		let log: DigestItem<T::Hash> = DigestItem::Consensus(
			BABE_ENGINE_ID,
			ConsensusLog::OnDisabled(i as u32).encode(),
		);
		<frame_system::Module<T>>::deposit_log(log.into());
	}

	fn make_randomness(vrf_output: VRFOutput) {
		// Reconstruct the bytes of VRFInOut using the authority id.
		Authorities::get()
			.get(primary.authority_index as usize)
			.and_then(|author| {
				schnorrkel::PublicKey::from_bytes(author.0.as_slice()).ok()
			})
			.and_then(|pubkey| {
				let transcript = sp_consensus_babe::make_transcript(
					&Self::randomness(),
					current_slot,
					EpochIndex::get(),
				);

				primary.vrf_output.0.attach_input_hash(
					&pubkey,
					transcript
				).ok()
			})
			.map(|inout| {
				inout.make_bytes(&sp_consensus_babe::BABE_VRF_INOUT_CONTEXT)
			})
	}
}

impl RawPreDigestT for RawPreDigest {
	type SlotNumber = SlotNumber;

	fn vrf_output(&self) -> Option<schnorrkel::RawVRFOutput> {
		if let RawPreDigest::Primary(ref primary) = self {
			Some(primary.vrf_output.clone())
		} else {
			None
		}
	}

	fn slot_number(&self) -> SlotNumber {
		self.slot_number()
	}
}

pub struct BabeFindAuthor<T: BabeTrait>(PhantomData<T>);

impl<T: BabeTrait> FindAuthor<u32> for BabeFindAuthor<T> {
	fn find_author<'a, I>(digests: I) -> Option<u32> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (id, mut data) in digests.into_iter() {
			if id == BABE_ENGINE_ID {
				let pre_digest: PreDigest = PreDigest::decode(&mut data).ok()?;
				return Some(pre_digest.authority_index())
			}
		}

		return None;
	}
}
