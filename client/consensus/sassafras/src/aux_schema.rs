use codec::{Encode, Decode};
use sp_core::H256;
use sp_consensus_sassafras::{
	EpochNumber, SlotNumber, SassafrasBlockWeight, SassafrasAuthorityWeight,
	VRFProof, Randomness, AuthorityId
};
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sc_client_api::AuxStore;

#[derive(Clone, Debug, Encode, Decode, Default)]
pub struct PoolAuxiliary {
	pub proofs: Vec<VRFProof>,
	pub authorities: Vec<(AuthorityId, SassafrasAuthorityWeight)>,
	pub randomness: Randomness,
	pub epoch: EpochNumber,
}

#[derive(Clone, Debug, Encode, Decode, Default)]
pub struct Auxiliary {
	pub total_weight: SassafrasBlockWeight,
	pub weight: SassafrasBlockWeight,
	pub slot: SlotNumber,

	pub publishing: PoolAuxiliary,
	pub validating: PoolAuxiliary,
}

pub const AUXILIARY_KEY: &[u8] = b"sassafras_auxiliary";

fn load_decode<B, T>(backend: &B, key: &[u8]) -> ClientResult<Option<T>>
	where
		B: AuxStore,
		T: Decode,
{
	let corrupt = |e: codec::Error| {
		ClientError::Backend(format!("Sassafras DB is corrupted. Decode error: {}", e.what()))
	};
	match backend.get_aux(key)? {
		None => Ok(None),
		Some(t) => T::decode(&mut &t[..]).map(Some).map_err(corrupt)
	}
}

pub(crate) fn load_auxiliary<B: AuxStore>(
	hash: &H256,
	backend: &B
) -> ClientResult<Auxiliary> {
	let auxiliary = load_decode::<_, Auxiliary>(backend, AUXILIARY_KEY)?
		.map(Into::into)
		.unwrap_or_default();

	Ok(auxiliary)
}

pub(crate) fn write_auxiliary<F, R>(
	auxiliary: &Auxiliary,
	write_aux: F,
) -> R where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	let encoded_auxiliary = auxiliary.encode();
	write_aux(
		&[(AUXILIARY_KEY, encoded_auxiliary.as_slice())],
	)
}
