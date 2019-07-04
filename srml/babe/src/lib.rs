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

//! Consensus extension module for BABE consensus.

#![cfg_attr(not(feature = "std"), no_std)]
#![forbid(unused_must_use, unsafe_code, unused_variables, dead_code)]
pub use timestamp;

use rstd::{result, prelude::*};
use srml_support::{decl_storage, decl_module, StorageValue, traits::FindAuthor};
use timestamp::{OnTimestampSet, Trait};
use primitives::{generic::DigestItem, traits::{SaturatedConversion, Saturating, RandomnessBeacon}};
use primitives::ConsensusEngineId;
#[cfg(feature = "std")]
use timestamp::TimestampInherentData;
use parity_codec::{Encode, Decode};
use inherents::{RuntimeString, InherentIdentifier, InherentData, ProvideInherent, MakeFatalError};
#[cfg(feature = "std")]
use inherents::{InherentDataProviders, ProvideInherentData};
use babe_primitives::BABE_ENGINE_ID;
pub use babe_primitives::{AuthorityId, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH, PUBLIC_KEY_LENGTH};

/// The BABE inherent identifier.
pub const INHERENT_IDENTIFIER: InherentIdentifier = *b"babeslot";

/// The type of the BABE inherent.
pub type InherentType = u64;

/// Auxiliary trait to extract BABE inherent data.
pub trait BabeInherentData {
	/// Get BABE inherent data.
	fn babe_inherent_data(&self) -> result::Result<InherentType, RuntimeString>;
	/// Replace BABE inherent data.
	fn babe_replace_inherent_data(&mut self, new: InherentType);
}

impl BabeInherentData for InherentData {
	fn babe_inherent_data(&self) -> result::Result<InherentType, RuntimeString> {
		self.get_data(&INHERENT_IDENTIFIER)
			.and_then(|r| r.ok_or_else(|| "BABE inherent data not found".into()))
	}

	fn babe_replace_inherent_data(&mut self, new: InherentType) {
		self.replace_data(INHERENT_IDENTIFIER, &new);
	}
}

/// Provides the slot duration inherent data for BABE.
#[cfg(feature = "std")]
pub struct InherentDataProvider {
	slot_duration: u64,
}

#[cfg(feature = "std")]
impl InherentDataProvider {
	/// Constructs `Self`
	pub fn new(slot_duration: u64) -> Self {
		Self {
			slot_duration
		}
	}
}

#[cfg(feature = "std")]
impl ProvideInherentData for InherentDataProvider {
	fn on_register(
		&self,
		providers: &InherentDataProviders,
	) -> result::Result<(), RuntimeString> {
		if !providers.has_provider(&timestamp::INHERENT_IDENTIFIER) {
			// Add the timestamp inherent data provider, as we require it.
			providers.register_provider(timestamp::InherentDataProvider)
		} else {
			Ok(())
		}
	}

	fn inherent_identifier(&self) -> &'static inherents::InherentIdentifier {
		&INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(
		&self,
		inherent_data: &mut InherentData,
	) -> result::Result<(), RuntimeString> {
		let timestamp = inherent_data.timestamp_inherent_data()?;
		let slot_num = timestamp / self.slot_duration;
		inherent_data.put_data(INHERENT_IDENTIFIER, &slot_num)
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		RuntimeString::decode(&mut &error[..]).map(Into::into)
	}
}

/// The length of the BABE randomness
pub const RANDOMNESS_LENGTH: usize = 32;

decl_storage! {
	trait Store for Module<T: Trait> as Babe {
		/// The last timestamp.
		LastTimestamp get(last): T::Moment;

		/// The current authorities set.
		Authorities get(authorities): Vec<AuthorityId>;

		/// The epoch randomness.
		///
		/// # Security
		///
		/// This MUST NOT be used for gambling, as it can be influenced by a
		/// malicious validator in the short term. It MAY be used in many
		/// cryptographic protocols, however, so long as one remembers that this
		/// (like everything else on-chain) it is public. For example, it can be
		/// used where a number is needed that cannot have been chosen by an
		/// adversary, for purposes such as public-coin zero-knowledge proofs.
		EpochRandomness get(epoch_randomness): [u8; 32];

		/// The randomness under construction
		UnderConstruction: [u8; 32];

		/// The randomness for the next epoch
		NextEpochRandomness: [u8; 32];

		/// The current epoch
		EpochIndex get(epoch_index): u64;
	}
}

decl_module! {
	/// The BABE SRML module
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {
		/// Initialization
		fn on_initialize() {
			for i in Self::get_inherent_digests()
				.logs
				.iter()
				.filter_map(|s| s.as_pre_runtime())
				.filter_map(|(id, mut data)| if id == BABE_ENGINE_ID {
					<[u8; VRF_OUTPUT_LENGTH]>::decode(&mut data)
				} else {
					None
				}) {
				Self::deposit_vrf_output(&i);
			}
		}
	}
}

impl<T: Trait> RandomnessBeacon for Module<T> {
	fn random() -> [u8; 32] {
		Self::epoch_randomness()
	}
}

/// A BABE public key
pub type BabeKey = [u8; PUBLIC_KEY_LENGTH];

impl<T: Trait> FindAuthor<u64> for Module<T> {
	fn find_author<'a, I>(digests: I) -> Option<u64> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (id, mut data) in digests.into_iter() {
			if id == BABE_ENGINE_ID {
				let (_, _, i): (
					[u8; VRF_OUTPUT_LENGTH],
					[u8; VRF_PROOF_LENGTH],
					u64,
				) = Decode::decode(&mut data)?;
				return Some(i)
			}
		}
		return None
	}
}

impl<T: Trait> Module<T> {
	/// Determine the BABE slot duration based on the Timestamp module configuration.
	pub fn slot_duration() -> T::Moment {
		// we double the minimum block-period so each author can always propose within
		// the majority of their slot.
		<timestamp::Module<T>>::minimum_period().saturating_mul(2.into())
	}

	fn change_authorities(new: Vec<AuthorityId>) {
		Authorities::put(&new);

		let log: DigestItem<T::Hash> = DigestItem::Consensus(BABE_ENGINE_ID, new.encode());
		<system::Module<T>>::deposit_log(log.into());
	}

	fn deposit_vrf_output(vrf_output: &[u8; VRF_OUTPUT_LENGTH]) {
		UnderConstruction::mutate(|z| z.iter_mut().zip(vrf_output).for_each(|(x, y)| *x^=y))
	}

	fn get_inherent_digests() -> system::DigestOf<T> {
		<system::Module<T>>::digest()
	}
}

impl<T: Trait> OnTimestampSet<T::Moment> for Module<T> {
	fn on_timestamp_set(_moment: T::Moment) { }
}

impl<T: Trait> session::OneSessionHandler<T::AccountId> for Module<T> {
	type Key = AuthorityId;
	fn on_new_session<'a, I: 'a>(changed: bool, validators: I)
		where I: Iterator<Item=(&'a T::AccountId, AuthorityId)>
	{
		// instant changes
		if changed {
			let next_authorities = validators.map(|(_, k)| k).collect::<Vec<_>>();
			let last_authorities = <Module<T>>::authorities();
			if next_authorities != last_authorities {
				Self::change_authorities(next_authorities);
			}
		}

		let rho = UnderConstruction::get();
		UnderConstruction::put([0; 32]);
		let last_epoch_randomness = EpochRandomness::get();
		let epoch_index = EpochIndex::get()
			.checked_add(1)
			.expect("epoch indices will never reach 2^64 before the death of the universe; qed");
		EpochIndex::put(epoch_index);
		EpochRandomness::put(NextEpochRandomness::get());
		let mut s = [0; 72];
		s[..32].copy_from_slice(&last_epoch_randomness);
		s[32..40].copy_from_slice(&epoch_index.to_le_bytes());
		s[40..].copy_from_slice(&rho);
		NextEpochRandomness::put(runtime_io::blake2_256(&s))
	}
	fn on_disabled(_i: usize) {
		// ignore?
	}
}

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = timestamp::Call<T>;
	type Error = MakeFatalError<RuntimeString>;
	const INHERENT_IDENTIFIER: InherentIdentifier = INHERENT_IDENTIFIER;

	fn create_inherent(_: &InherentData) -> Option<Self::Call> {
		None
	}

	fn check_inherent(call: &Self::Call, data: &InherentData) -> result::Result<(), Self::Error> {
		let timestamp = match call {
			timestamp::Call::set(ref timestamp) => timestamp.clone(),
			_ => return Ok(()),
		};

		let timestamp_based_slot = (timestamp / Self::slot_duration()).saturated_into::<u64>();
		let seal_slot = data.babe_inherent_data()?;
		if timestamp_based_slot == seal_slot {
			Ok(())
		} else {
			Err(RuntimeString::from("timestamp set in block doesn’t match slot in seal").into())
		}
	}
}
