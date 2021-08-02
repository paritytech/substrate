#![cfg_attr(not(feature = "std"), no_std)]

use codec::Decode;
use codec::Encode;
use sp_inherents::{InherentData, InherentIdentifier};
use sp_runtime::RuntimeString;

#[cfg(feature = "std")]
use sp_inherents::ProvideInherentData;

pub const IGNORE_TX_INHERENT_IDENTIFIER: InherentIdentifier = *b"ignoreTX";

pub fn extract_inherent_data(data: &InherentData) -> Result<bool, RuntimeString> {
	data.get_data::<bool>(&IGNORE_TX_INHERENT_IDENTIFIER)
		.map_err(|_| RuntimeString::from("Invalid inherent data encoding."))?
		.ok_or_else(|| "Ignore Transaction flag is not provided.".into())
}

#[cfg(feature = "std")]
pub struct IgnoreTXInherentDataProvider(pub bool);

#[derive(Encode, sp_runtime::RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum IgnoreTXInherentError {
	Other(RuntimeString),
}

impl IgnoreTXInherentError {
	/// Try to create an instance ouf of the given identifier and data.
	#[cfg(feature = "std")]
	pub fn try_from(id: &InherentIdentifier, data: &[u8]) -> Option<Self> {
		if id == &IGNORE_TX_INHERENT_IDENTIFIER {
			<IgnoreTXInherentError as codec::Decode>::decode(&mut &data[..]).ok()
		} else {
			None
		}
	}
}

#[cfg(feature = "std")]
impl ProvideInherentData for IgnoreTXInherentDataProvider {
	fn inherent_identifier(&self) -> &'static InherentIdentifier {
		&IGNORE_TX_INHERENT_IDENTIFIER
	}

	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), sp_inherents::Error> {
		inherent_data.put_data(IGNORE_TX_INHERENT_IDENTIFIER, &self.0)
	}

	fn error_to_string(&self, error: &[u8]) -> Option<String> {
		IgnoreTXInherentError::try_from(&IGNORE_TX_INHERENT_IDENTIFIER, error).map(|e| format!("{:?}", e))
	}
}
