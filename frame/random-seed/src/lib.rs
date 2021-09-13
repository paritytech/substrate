#![cfg_attr(not(feature = "std"), no_std)]

use codec::Decode;
use codec::Encode;
use sp_core::ShufflingSeed;
use sp_inherents::{InherentData, InherentIdentifier};
use sp_runtime::RuntimeString;

#[cfg(feature = "std")]
use sp_inherents::ProvideInherentData;

// originally in sp-module
pub const RANDOM_SEED_INHERENT_IDENTIFIER: InherentIdentifier = *b"blckseed";

#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum RandomSeedInherentError {
	Other(RuntimeString),
}

impl RandomSeedInherentError {
	/// Try to create an instance ouf of the given identifier and data.
	#[cfg(feature = "std")]
	pub fn try_from(id: &InherentIdentifier, data: &[u8]) -> Option<Self> {
		if id == &RANDOM_SEED_INHERENT_IDENTIFIER {
			<RandomSeedInherentError as codec::Decode>::decode(&mut &data[..]).ok()
		} else {
			None
		}
	}
}

pub fn extract_inherent_data(data: &InherentData) -> Result<ShufflingSeed, RuntimeString> {
	data.get_data::<ShufflingSeed>(&RANDOM_SEED_INHERENT_IDENTIFIER)
		.map_err(|_| RuntimeString::from("Invalid random seed inherent data encoding."))?
		.ok_or_else(|| "Random Seed inherent data is not provided.".into())
}

#[cfg(feature = "std")]
pub struct RandomSeedInherentDataProvider(pub ShufflingSeed);

#[cfg(feature = "std")]
impl ProvideInherentData for RandomSeedInherentDataProvider {
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&RANDOM_SEED_INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), sp_inherents::Error> {
		inherent_data.put_data(RANDOM_SEED_INHERENT_IDENTIFIER, &self.0)
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		RandomSeedInherentError::try_from(&RANDOM_SEED_INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}

