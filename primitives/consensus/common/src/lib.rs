// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Common utilities for building and using consensus engines in substrate.
//!
//! Much of this crate is _unstable_ and thus the API is likely to undergo
//! change. Implementors of traits should not rely on the interfaces to remain
//! the same.

use std::{sync::Arc, time::Duration};

use futures::prelude::*;
use sp_runtime::{
	traits::{Block as BlockT, HashingFor},
	Digest,
};
use sp_state_machine::StorageProof;

pub mod block_validation;
pub mod error;
mod select_chain;

pub use self::error::Error;
pub use select_chain::SelectChain;
pub use sp_inherents::InherentData;
pub use sp_state_machine::Backend as StateBackend;

/// Block status.
#[derive(Debug, PartialEq, Eq)]
pub enum BlockStatus {
	/// Added to the import queue.
	Queued,
	/// Already in the blockchain and the state is available.
	InChainWithState,
	/// In the blockchain, but the state is not available.
	InChainPruned,
	/// Block or parent is known to be bad.
	KnownBad,
	/// Not in the queue or the blockchain.
	Unknown,
}

/// Block data origin.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum BlockOrigin {
	/// Genesis block built into the client.
	Genesis,
	/// Block is part of the initial sync with the network.
	NetworkInitialSync,
	/// Block was broadcasted on the network.
	NetworkBroadcast,
	/// Block that was received from the network and validated in the consensus process.
	ConsensusBroadcast,
	/// Block that was collated by this node.
	Own,
	/// Block was imported from a file.
	File,
}

/// Environment for a Consensus instance.
///
/// Creates proposer instance.
pub trait Environment<B: BlockT> {
	/// The proposer type this creates.
	type Proposer: Proposer<B> + Send + 'static;
	/// A future that resolves to the proposer.
	type CreateProposer: Future<Output = Result<Self::Proposer, Self::Error>>
		+ Send
		+ Unpin
		+ 'static;
	/// Error which can occur upon creation.
	type Error: From<Error> + std::error::Error + 'static;

	/// Initialize the proposal logic on top of a specific header. Provide
	/// the authorities at that header.
	fn init(&mut self, parent_header: &B::Header) -> Self::CreateProposer;
}

/// A proposal that is created by a [`Proposer`].
pub struct Proposal<Block: BlockT, Proof> {
	/// The block that was build.
	pub block: Block,
	/// Proof that was recorded while building the block.
	pub proof: Proof,
	/// The storage changes while building this block.
	pub storage_changes: sp_state_machine::StorageChanges<HashFor<Block>>,
}

/// Error that is returned when [`ProofRecording`] requested to record a proof,
/// but no proof was recorded.
#[derive(Debug, thiserror::Error)]
#[error("Proof should be recorded, but no proof was provided.")]
pub struct NoProofRecorded;

/// A trait to express the state of proof recording on type system level.
///
/// This is used by [`Proposer`] to signal if proof recording is enabled. This can be used by
/// downstream users of the [`Proposer`] trait to enforce that proof recording is activated when
/// required. The only two implementations of this trait are [`DisableProofRecording`] and
/// [`EnableProofRecording`].
///
/// This trait is sealed and can not be implemented outside of this crate!
pub trait ProofRecording: Send + Sync + private::Sealed + 'static {
	/// The proof type that will be used internally.
	type Proof: Send + Sync + 'static;
	/// Is proof recording enabled?
	const ENABLED: bool;
	/// Convert the given `storage_proof` into [`Self::Proof`].
	///
	/// Internally Substrate uses `Option<StorageProof>` to express the both states of proof
	/// recording (for now) and as [`Self::Proof`] is some different type, we need to provide a
	/// function to convert this value.
	///
	/// If the proof recording was requested, but `None` is given, this will return
	/// `Err(NoProofRecorded)`.
	fn into_proof(storage_proof: Option<StorageProof>) -> Result<Self::Proof, NoProofRecorded>;
}

/// Express that proof recording is disabled.
///
/// For more information see [`ProofRecording`].
pub struct DisableProofRecording;

impl ProofRecording for DisableProofRecording {
	type Proof = ();
	const ENABLED: bool = false;

	fn into_proof(_: Option<StorageProof>) -> Result<Self::Proof, NoProofRecorded> {
		Ok(())
	}
}

/// Express that proof recording is enabled.
///
/// For more information see [`ProofRecording`].
pub struct EnableProofRecording;

impl ProofRecording for EnableProofRecording {
	type Proof = sp_state_machine::StorageProof;
	const ENABLED: bool = true;

	fn into_proof(proof: Option<StorageProof>) -> Result<Self::Proof, NoProofRecorded> {
		proof.ok_or(NoProofRecorded)
	}
}

/// Provides `Sealed` trait to prevent implementing trait [`ProofRecording`] outside of this crate.
mod private {
	/// Special trait that prevents the implementation of [`super::ProofRecording`] outside of this
	/// crate.
	pub trait Sealed {}

	impl Sealed for super::DisableProofRecording {}
	impl Sealed for super::EnableProofRecording {}
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
///
/// Proposers are generic over bits of "consensus data" which are engine-specific.
pub trait Proposer<B: BlockT> {
	/// Error type which can occur when proposing or evaluating.
	type Error: From<Error> + std::error::Error + 'static;
	/// Future that resolves to a committed proposal with an optional proof.
	type Proposal: Future<Output = Result<Proposal<B, Self::Proof>, Self::Error>>
		+ Send
		+ Unpin
		+ 'static;
	/// The supported proof recording by the implementator of this trait. See [`ProofRecording`]
	/// for more information.
	type ProofRecording: self::ProofRecording<Proof = Self::Proof> + Send + Sync + 'static;
	/// The proof type used by [`Self::ProofRecording`].
	type Proof: Send + Sync + 'static;

	/// Create a proposal.
	///
	/// Gets the `inherent_data` and `inherent_digests` as input for the proposal. Additionally
	/// a maximum duration for building this proposal is given. If building the proposal takes
	/// longer than this maximum, the proposal will be very likely discarded.
	///
	/// If `block_size_limit` is given, the proposer should push transactions until the block size
	/// limit is hit. Depending on the `finalize_block` implementation of the runtime, it probably
	/// incorporates other operations (that are happening after the block limit is hit). So,
	/// when the block size estimation also includes a proof that is recorded alongside the block
	/// production, the proof can still grow. This means that the `block_size_limit` should not be
	/// the hard limit of what is actually allowed.
	///
	/// # Return
	///
	/// Returns a future that resolves to a [`Proposal`] or to [`Error`].
	fn propose(
		self,
		inherent_data: InherentData,
		inherent_digests: Digest,
		max_duration: Duration,
		block_size_limit: Option<usize>,
	) -> Self::Proposal;
}

/// An oracle for when major synchronization work is being undertaken.
///
/// Generally, consensus authoring work isn't undertaken while well behind
/// the head of the chain.
pub trait SyncOracle {
	/// Whether the synchronization service is undergoing major sync.
	/// Returns true if so.
	fn is_major_syncing(&self) -> bool;
	/// Whether the synchronization service is offline.
	/// Returns true if so.
	fn is_offline(&self) -> bool;
}

/// A synchronization oracle for when there is no network.
#[derive(Clone, Copy, Debug)]
pub struct NoNetwork;

impl SyncOracle for NoNetwork {
	fn is_major_syncing(&self) -> bool {
		false
	}
	fn is_offline(&self) -> bool {
		false
	}
}

impl<T> SyncOracle for Arc<T>
where
	T: ?Sized,
	T: SyncOracle,
{
	fn is_major_syncing(&self) -> bool {
		T::is_major_syncing(self)
	}

	fn is_offline(&self) -> bool {
		T::is_offline(self)
	}
}
