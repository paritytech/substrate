use std::sync::Arc;
use parking_lot::Mutex;
use codec::{Encode, Decode};
use log::info;
use sp_runtime::traits::Block as BlockT;
use sp_blockchain::{Result as ClientResult, Error as ClientError};
use sc_client_api::AuxStore;
use sc_consensus_epochs::{SharedEpochChanges, EpochChangesFor};
use crate::Epoch;

const SASSAFRAS_EPOCH_CHANGES: &[u8] = b"sassafras_epoch_changes";

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

/// Load or initialize persistent epoch change data from backend.
pub(crate) fn load_epoch_changes<Block: BlockT, B: AuxStore>(
	backend: &B,
) -> ClientResult<SharedEpochChanges<Block, Epoch>> {
	let epoch_changes = load_decode::<_, EpochChangesFor<Block, Epoch>>(
		backend, SASSAFRAS_EPOCH_CHANGES
	)?
		.map(|v| Arc::new(Mutex::new(v)))
		.unwrap_or_else(|| {
			info!(target: "sassafras",
				"Creating empty Sassafras epoch changes on what appears to be first startup."
			);
			SharedEpochChanges::<Block, Epoch>::default()
		});

	// rebalance the tree after deserialization. this isn't strictly necessary
	// since the tree is now rebalanced on every update operation. but since the
	// tree wasn't rebalanced initially it's useful to temporarily leave it here
	// to avoid having to wait until an import for rebalancing.
	epoch_changes.lock().rebalance();

	Ok(epoch_changes)
}

/// Update the epoch changes on disk after a change.
pub(crate) fn write_epoch_changes<Block: BlockT, F, R>(
	epoch_changes: &EpochChangesFor<Block, Epoch>,
	write_aux: F,
) -> R where
	F: FnOnce(&[(&'static [u8], &[u8])]) -> R,
{
	let encoded_epoch_changes = epoch_changes.encode();
	write_aux(
		&[(SASSAFRAS_EPOCH_CHANGES, encoded_epoch_changes.as_slice())],
	)
}
