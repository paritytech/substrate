#![cfg_attr(not(feature = "std"), no_std)]

use codec::Decode;
use codec::Encode;
use frame_support::{decl_module, decl_storage, weights::DispatchClass};
use sp_inherents::{InherentData, InherentIdentifier, IsFatalError, ProvideInherent};
use sp_runtime::RuntimeString;

#[cfg(feature = "std")]
use sp_inherents::ProvideInherentData;

/// The module configuration trait
pub trait Trait: frame_system::Trait {}

#[derive(Encode, Decode, Debug, Clone, PartialEq)]
pub struct SeedType {
	pub seed: [u8; 32],
	pub proof: [u8; 64],
}

impl Default for SeedType {
	fn default() -> Self {
		SeedType {
			seed: Default::default(),
			proof: [0_u8; 64],
		}
	}
}

decl_module! {
	pub struct Module<T: Trait> for enum Call where origin: T::Origin {

		#[weight =  (
			10_000,
			DispatchClass::Mandatory
		)]
		fn set(origin, seed: SeedType) {
			log::debug!(target: "mat", "set seed: ${:X?}", seed);
			<Self as Store>::Seed::put(seed);
		}

	}
}

decl_storage! {
	trait Store for Module<T: Trait> as RandomSeed {
		/// Current time for the current block.
		pub Seed get(fn seed) : SeedType;
	}
	add_extra_genesis {
		#[allow(clippy::type_complexity)]
		config(random_seed): [u8; 32];
		build(|config: &GenesisConfig|{
			Seed::set(SeedType{
				seed: config.random_seed,
				proof: [0_u8; 64]
			});
		});
	}
}

impl<T: Trait> Module<T> {
	pub fn get() -> SeedType {
		Self::seed()
	}
}

// originally in sp-module
pub type RandomSeedInherentType = SeedType;
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

impl IsFatalError for RandomSeedInherentError {
	fn is_fatal_error(&self) -> bool {
		true
	}
}

pub fn extract_inherent_data(data: &InherentData) -> Result<RandomSeedInherentType, RuntimeString> {
	data.get_data::<RandomSeedInherentType>(&RANDOM_SEED_INHERENT_IDENTIFIER)
		.map_err(|_| RuntimeString::from("Invalid random seed inherent data encoding."))?
		.ok_or_else(|| "Random Seed inherent data is not provided.".into())
}

#[cfg(feature = "std")]
pub struct RandomSeedInherentDataProvider(pub SeedType);

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

impl<T: Trait> ProvideInherent for Module<T> {
	type Call = Call<T>;
	type Error = RandomSeedInherentError;
	const INHERENT_IDENTIFIER: InherentIdentifier = *b"blckseed";

	fn create_inherent(data: &InherentData) -> Option<Self::Call> {
		log::debug!(target: "rand-seed", "initializing random seed");
		let seed: SeedType = extract_inherent_data(data).expect("Gets and decodes random seed");
		Some(Call::set(seed))
	}

	fn check_inherent(_call: &Self::Call, _data: &InherentData) -> Result<(), Self::Error> {
		Ok(())
	}
}
