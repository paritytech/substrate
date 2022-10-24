// This file is part of Substrate.

// This file is part of SubstrateNonepyright (C) 2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! # Sassafras
//!
//! TODO-SASS-P2: documentation

// TODO-SASS-P2: remove this
//#![deny(warnings)]
#![forbid(unsafe_code, missing_docs)]

use std::{
	collections::{BTreeMap, HashMap},
	future::Future,
	sync::Arc,
	task::{Context, Poll},
	time::Duration,
};

use futures::{
	channel::mpsc::{channel, Receiver, Sender},
	prelude::*,
};
use log::{debug, error, info, log, trace, warn};
use parking_lot::Mutex;
use prometheus_endpoint::Registry;
use scale_codec::{Decode, Encode};
use schnorrkel::SignatureError;

use sc_client_api::{
	backend::AuxStore, BlockchainEvents, PreCommitActions, ProvideUncles, UsageProvider,
};
use sc_consensus::{
	block_import::{
		BlockCheckParams, BlockImport, BlockImportParams, ForkChoiceStrategy, ImportResult,
		StateAction,
	},
	import_queue::{BasicQueue, BoxJustificationImport, DefaultImportQueue},
	Verifier,
};
use sc_consensus_epochs::{
	descendent_query, Epoch as EpochT, EpochChangesFor, EpochIdentifier, EpochIdentifierPosition,
	SharedEpochChanges, ViableEpochDescriptor,
};
use sc_consensus_slots::{CheckedHeader, InherentDataProviderExt, SlotInfo, StorageChanges};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG, CONSENSUS_TRACE};
use sp_api::{ApiExt, ProvideRuntimeApi};
use sp_application_crypto::AppKey;
use sp_block_builder::BlockBuilder as BlockBuilderApi;
use sp_blockchain::{Error as ClientError, HeaderBackend, HeaderMetadata, Result as ClientResult};
use sp_consensus::{
	BlockOrigin, CacheKeyId, Environment, Error as ConsensusError, Proposer, SelectChain,
	SyncOracle,
};
use sp_consensus_slots::Slot;
use sp_core::{crypto::ByteArray, ExecutionContext, Pair};
use sp_inherents::{CreateInherentDataProviders, InherentData, InherentDataProvider};
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::{BlockId, OpaqueDigestItemId},
	traits::{Block as BlockT, Header, NumberFor, One, Zero},
	DigestItem,
};

// Re-export Sassafras primitives.
pub use sp_consensus_sassafras::{
	digests::{CompatibleDigestItem, ConsensusLog, NextEpochDescriptor, PreDigest},
	inherents::SassafrasInherentData,
	vrf::{make_slot_transcript, make_ticket_transcript},
	AuthorityId, AuthorityIndex, AuthorityPair, AuthoritySignature, SassafrasApi,
	SassafrasAuthorityWeight, SassafrasConfiguration, SassafrasEpochConfiguration, Ticket,
	TicketAux, VRFOutput, VRFProof, SASSAFRAS_ENGINE_ID, VRF_OUTPUT_LENGTH, VRF_PROOF_LENGTH,
};

mod authorship;
mod aux_schema;
mod block_import;
#[cfg(test)]
mod tests;
mod verification;

// Export core components.
pub use authorship::{start_sassafras, SassafrasWorker, SassafrasWorkerParams};
pub use aux_schema::revert;
pub use block_import::{block_import, SassafrasBlockImport};
pub use verification::SassafrasVerifier;

/// Errors encountered by the Sassafras routines.
#[derive(Debug, thiserror::Error)]
pub enum Error<B: BlockT> {
	/// Multiple Sassafras pre-runtime digests
	#[error("Multiple Sassafras pre-runtime digests")]
	MultiplePreRuntimeDigests,
	/// No Sassafras pre-runtime digest found
	#[error("No Sassafras pre-runtime digest found")]
	NoPreRuntimeDigest,
	/// Multiple Sassafras epoch change digests
	#[error("Multiple Sassafras epoch change digests")]
	MultipleEpochChangeDigests,
	/// Could not fetch epoch
	#[error("Could not fetch epoch at {0:?}")]
	FetchEpoch(B::Hash),
	/// Header rejected: too far in the future
	#[error("Header {0:?} rejected: too far in the future")]
	TooFarInFuture(B::Hash),
	/// Parent unavailable. Cannot import
	#[error("Parent ({0}) of {1} unavailable. Cannot import")]
	ParentUnavailable(B::Hash, B::Hash),
	/// Slot number must increase
	#[error("Slot number must increase: parent slot: {0}, this slot: {1}")]
	SlotMustIncrease(Slot, Slot),
	/// Header has a bad seal
	#[error("Header {0:?} has a bad seal")]
	HeaderBadSeal(B::Hash),
	/// Header is unsealed
	#[error("Header {0:?} is unsealed")]
	HeaderUnsealed(B::Hash),
	/// Slot author not found
	#[error("Slot author not found")]
	SlotAuthorNotFound,
	/// Bad signature
	#[error("Bad signature on {0:?}")]
	BadSignature(B::Hash),
	/// VRF verification failed
	#[error("VRF verification failed: {0:?}")]
	VRFVerificationFailed(SignatureError),
	/// Unexpected authoring mechanism
	#[error("Unexpected authoring mechanism")]
	UnexpectedAuthoringMechanism,
	/// Could not fetch parent header
	#[error("Could not fetch parent header: {0}")]
	FetchParentHeader(sp_blockchain::Error),
	/// Expected epoch change to happen.
	#[error("Expected epoch change to happen at {0:?}, s{1}")]
	ExpectedEpochChange(B::Hash, Slot),
	/// Unexpected epoch change
	#[error("Unexpected epoch change")]
	UnexpectedEpochChange,
	/// Parent block has no associated weight
	#[error("Parent block of {0} has no associated weight")]
	ParentBlockNoAssociatedWeight(B::Hash),
	/// Check inherents error
	#[error("Checking inherents failed: {0}")]
	CheckInherents(sp_inherents::Error),
	/// Unhandled check inherents error
	#[error("Checking inherents unhandled error: {}", String::from_utf8_lossy(.0))]
	CheckInherentsUnhandled(sp_inherents::InherentIdentifier),
	/// Create inherents error.
	#[error("Creating inherents failed: {0}")]
	CreateInherents(sp_inherents::Error),
	/// Client error
	#[error(transparent)]
	Client(sp_blockchain::Error),
	/// Runtime Api error.
	#[error(transparent)]
	RuntimeApi(sp_api::ApiError),
	/// Fork tree error
	#[error(transparent)]
	ForkTree(Box<fork_tree::Error<sp_blockchain::Error>>),
}

impl<B: BlockT> From<Error<B>> for String {
	fn from(error: Error<B>) -> String {
		error.to_string()
	}
}

// Convenience function
fn sassafras_err<B: BlockT>(error: Error<B>) -> Error<B> {
	error!(target: "sassafras", "🌳 {}", error);
	error
}

/// Sassafras epoch information
#[derive(Encode, Decode, PartialEq, Eq, Clone, Debug)]
pub struct Epoch {
	/// The epoch index.
	pub epoch_idx: u64,
	/// The starting slot of the epoch.
	pub start_slot: Slot,
	/// Epoch configuration
	pub config: SassafrasConfiguration,
	/// Tickets auxiliary data.
	pub tickets_aux: BTreeMap<Ticket, (AuthorityIndex, TicketAux)>,
}

impl EpochT for Epoch {
	type NextEpochDescriptor = NextEpochDescriptor;
	type Slot = Slot;

	fn increment(&self, descriptor: NextEpochDescriptor) -> Epoch {
		let config = SassafrasConfiguration {
			slot_duration: self.config.slot_duration,
			epoch_duration: self.config.epoch_duration,
			authorities: descriptor.authorities,
			randomness: descriptor.randomness,
			threshold_params: descriptor.config.unwrap_or(self.config.threshold_params.clone()),
		};
		Epoch {
			epoch_idx: self.epoch_idx + 1,
			start_slot: self.start_slot + config.epoch_duration,
			config,
			tickets_aux: BTreeMap::new(),
		}
	}

	fn start_slot(&self) -> Slot {
		self.start_slot
	}

	fn end_slot(&self) -> Slot {
		self.start_slot + self.config.epoch_duration
	}
}

impl Epoch {
	/// Create the genesis epoch (epoch #0). This is defined to start at the slot of
	/// the first block, so that has to be provided.
	pub fn genesis(config: &SassafrasConfiguration, slot: Slot) -> Epoch {
		Epoch {
			epoch_idx: 0,
			start_slot: slot,
			config: config.clone(),
			tickets_aux: BTreeMap::new(),
		}
	}
}

/// Read latest finalized protocol configuration.
pub fn configuration<B, C>(client: &C) -> ClientResult<SassafrasConfiguration>
where
	B: BlockT,
	C: ProvideRuntimeApi<B> + UsageProvider<B>,
	C::Api: SassafrasApi<B>,
{
	let info = client.usage_info().chain;
	let hash = info.finalized_state.map(|(hash, _)| hash).unwrap_or_else(|| {
		debug!(target: "sassafras", "🌳 Reading config from genesis");
		info.genesis_hash
	});

	let config = client.runtime_api().configuration(&BlockId::Hash(hash))?;
	Ok(config)
}

/// Intermediate value passed to block importer from authoring or validation logic.
pub struct SassafrasIntermediate<B: BlockT> {
	/// The epoch descriptor.
	pub epoch_descriptor: ViableEpochDescriptor<B::Hash, NumberFor<B>, Epoch>,
}

/// Intermediate key for Babe engine.
pub static INTERMEDIATE_KEY: &[u8] = b"sass1";

/// Extract the Sassafras pre digest from the given header. Pre-runtime digests are
/// mandatory, the function will return `Err` if none is found.
fn find_pre_digest<B: BlockT>(header: &B::Header) -> Result<PreDigest, Error<B>> {
	// Genesis block doesn't contain a pre digest so let's generate a
	// dummy one to not break any invariants in the rest of the code
	if header.number().is_zero() {
		const PROOF: &str = "zero sequence is a valid vrf output/proof; qed";
		let vrf_output = VRFOutput::try_from([0; VRF_OUTPUT_LENGTH]).expect(PROOF);
		let vrf_proof = VRFProof::try_from([0; VRF_PROOF_LENGTH]).expect(PROOF);
		return Ok(PreDigest {
			authority_idx: 0,
			slot: 0.into(),
			vrf_output,
			vrf_proof,
			ticket_aux: None,
		})
	}

	let mut pre_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "🌳 Checking log {:?}, looking for pre runtime digest", log);
		match (log.as_sassafras_pre_digest(), pre_digest.is_some()) {
			(Some(_), true) => return Err(sassafras_err(Error::MultiplePreRuntimeDigests)),
			(None, _) => trace!(target: "sassafras", "🌳 Ignoring digest not meant for us"),
			(s, false) => pre_digest = s,
		}
	}
	pre_digest.ok_or_else(|| sassafras_err(Error::NoPreRuntimeDigest))
}

/// Extract the Sassafras epoch change digest from the given header, if it exists.
fn find_next_epoch_digest<B: BlockT>(
	header: &B::Header,
) -> Result<Option<NextEpochDescriptor>, Error<B>> {
	let mut epoch_digest: Option<_> = None;
	for log in header.digest().logs() {
		trace!(target: "sassafras", "🌳 Checking log {:?}, looking for epoch change digest.", log);
		let log = log.try_to::<ConsensusLog>(OpaqueDigestItemId::Consensus(&SASSAFRAS_ENGINE_ID));
		match (log, epoch_digest.is_some()) {
			(Some(ConsensusLog::NextEpochData(_)), true) =>
				return Err(sassafras_err(Error::MultipleEpochChangeDigests)),
			(Some(ConsensusLog::NextEpochData(epoch)), false) => epoch_digest = Some(epoch),
			_ => trace!(target: "sassafras", "🌳 Ignoring digest not meant for us"),
		}
	}

	Ok(epoch_digest)
}

/// State that must be shared between the import queue and the authoring logic.
#[derive(Clone)]
pub struct SassafrasLink<B: BlockT> {
	/// Epoch changes tree
	epoch_changes: SharedEpochChanges<B, Epoch>,
	/// Startup configuration. Read from runtime at last finalized block.
	genesis_config: SassafrasConfiguration,
}

impl<B: BlockT> SassafrasLink<B> {
	/// Get the config of this link.
	pub fn genesis_config(&self) -> &SassafrasConfiguration {
		&self.genesis_config
	}
}

/// Start an import queue for the Sassafras consensus algorithm.
///
/// This method returns the import queue, some data that needs to be passed to the block authoring
/// logic (`SassafrasLink`), and a future that must be run to completion and is responsible for
/// listening to finality notifications and pruning the epoch changes tree.
///
/// The block import object provided must be the `SassafrasBlockImport` or a wrapper of it,
/// otherwise crucial import logic will be omitted.
pub fn import_queue<Block: BlockT, Client, SelectChain, BI, CIDP>(
	sassafras_link: SassafrasLink<Block>,
	block_import: BI,
	justification_import: Option<BoxJustificationImport<Block>>,
	client: Arc<Client>,
	select_chain: SelectChain,
	create_inherent_data_providers: CIDP,
	spawner: &impl sp_core::traits::SpawnEssentialNamed,
	registry: Option<&Registry>,
	telemetry: Option<TelemetryHandle>,
) -> ClientResult<DefaultImportQueue<Block, Client>>
where
	Client: ProvideRuntimeApi<Block>
		+ HeaderBackend<Block>
		+ HeaderMetadata<Block, Error = sp_blockchain::Error>
		+ AuxStore
		+ Send
		+ Sync
		+ 'static,
	Client::Api: BlockBuilderApi<Block> + SassafrasApi<Block> + ApiExt<Block>,
	BI: BlockImport<
			Block,
			Error = ConsensusError,
			Transaction = sp_api::TransactionFor<Client, Block>,
		> + Send
		+ Sync
		+ 'static,
	SelectChain: sp_consensus::SelectChain<Block> + 'static,
	CIDP: CreateInherentDataProviders<Block, ()> + Send + Sync + 'static,
	CIDP::InherentDataProviders: InherentDataProviderExt + Send + Sync,
{
	let verifier = SassafrasVerifier::new(
		client,
		select_chain,
		create_inherent_data_providers,
		sassafras_link.epoch_changes,
		telemetry,
		sassafras_link.genesis_config,
	);

	Ok(BasicQueue::new(verifier, Box::new(block_import), justification_import, spawner, registry))
}
