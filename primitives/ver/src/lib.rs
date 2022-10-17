#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};

use sp_core::crypto::key_types::AURA;
#[cfg(feature = "helpers")]
use sp_core::sr25519;
use sp_core::ShufflingSeed;
use sp_inherents::{InherentData, InherentIdentifier};
#[cfg(feature = "helpers")]
use sp_keystore::vrf::{VRFTranscriptData, VRFTranscriptValue};
#[cfg(feature = "helpers")]
use sp_keystore::SyncCryptoStore;
use sp_runtime::{traits::Block as BlockT, ConsensusEngineId, RuntimeString};
use sp_std::vec::Vec;

// originally in sp-module
pub const RANDOM_SEED_INHERENT_IDENTIFIER: InherentIdentifier = *b"blckseed";
pub const VER_ENGINE_ID: ConsensusEngineId = *b"_VER";

#[derive(Clone, Encode, Decode)]
pub struct PreDigestVer<Block: BlockT> {
	pub prev_extrisnics: Vec<<Block as BlockT>::Extrinsic>,
}

pub type EncodedTx = Vec<u8>;

pub fn extract_inherent_data(data: &InherentData) -> Result<ShufflingSeed, RuntimeString> {
	data.get_data::<ShufflingSeed>(&RANDOM_SEED_INHERENT_IDENTIFIER)
		.map_err(|_| RuntimeString::from("Invalid random seed inherent data encoding."))?
		.ok_or_else(|| "Random Seed inherent data is not provided.".into())
}

#[cfg(feature = "std")]
pub struct RandomSeedInherentDataProvider(pub ShufflingSeed);

#[cfg(feature = "helpers")]
pub fn calculate_next_seed<T: sp_keystore::SyncCryptoStore + ?Sized>(
	keystore: &T,
	public_key: &sr25519::Public,
	prev_seed: &ShufflingSeed,
) -> Option<ShufflingSeed> {
	calculate_next_seed_from_bytes::<T>(keystore, public_key, prev_seed.seed.as_bytes().to_vec())
}

#[cfg(feature = "helpers")]
pub fn calculate_next_seed_from_bytes<T: sp_keystore::SyncCryptoStore + ?Sized>(
	keystore: &T,
	public_key: &sr25519::Public,
	prev_seed: Vec<u8>,
) -> Option<ShufflingSeed> {
	let transcript = VRFTranscriptData {
		label: b"shuffling_seed",
		items: vec![("prev_seed", VRFTranscriptValue::Bytes(prev_seed))],
	};
	SyncCryptoStore::sr25519_vrf_sign(keystore, AURA, public_key, transcript.clone())
		.ok()
		.flatten()
		.map(|sig| ShufflingSeed {
			seed: sig.output.to_bytes().into(),
			proof: sig.proof.to_bytes().into(),
		})
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
impl sp_inherents::InherentDataProvider for RandomSeedInherentDataProvider {
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), sp_inherents::Error> {
		inherent_data.put_data(RANDOM_SEED_INHERENT_IDENTIFIER, &self.0)
	}

	async fn try_handle_error(&self, _: &InherentIdentifier, _: &[u8]) -> Option<Result<(), sp_inherents::Error>> {
		// There is no error anymore
		None
	}
}
