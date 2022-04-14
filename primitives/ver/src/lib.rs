#![cfg_attr(not(feature = "std"), no_std)]

use codec::{Decode, Encode};
use sp_core::ShufflingSeed;
use sp_inherents::{InherentData, InherentIdentifier};
use sp_runtime::{
	traits::{Block as BlockT, Header, One, Zero},
	ConsensusEngineId, DigestItem, RuntimeString,
};
use sp_std::vec::Vec;

// originally in sp-module
pub const RANDOM_SEED_INHERENT_IDENTIFIER: InherentIdentifier = *b"blckseed";
pub const VER_ENGINE_ID: ConsensusEngineId = *b"_VER";

#[derive(Clone, Encode, Decode)]
pub struct PreDigestVer<Block: BlockT> {
	pub prev_extrisnics: Vec<<Block as BlockT>::Extrinsic>,
}

pub trait CompatibleDigestItemVer<B: BlockT>: Sized {
	/// Construct a digest item which contains a BABE pre-digest.
	fn ver_pre_digest(seal: PreDigestVer<B>) -> Self;

	/// If this item is an BABE pre-digest, return it.
	fn as_ver_pre_digest(&self) -> Option<PreDigestVer<B>>;
}

impl<B: BlockT> CompatibleDigestItemVer<B> for DigestItem {
	fn ver_pre_digest(digest: PreDigestVer<B>) -> Self {
		DigestItem::PreRuntime(VER_ENGINE_ID, digest.encode())
	}

	fn as_ver_pre_digest(&self) -> Option<PreDigestVer<B>> {
		self.pre_runtime_try_to(&VER_ENGINE_ID)
	}
}

pub fn find_prev_extrinsics<B: BlockT>(header: &B::Header) -> Option<Vec<B::Extrinsic>> {
	// genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() || header.number().is_one() {
		return Some(Vec::new());
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		match (log.as_ver_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => {
				return None;
			}
			(s, false) => pre_digest = s,
			(None, _) => {}
		}
	}
	pre_digest.map(|digest: PreDigestVer<B>| digest.prev_extrisnics)
}

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
