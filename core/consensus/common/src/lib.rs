// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate Consensus Common.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Consensus Common is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Consensus Common.  If not, see <http://www.gnu.org/licenses/>.

//! Common utilities for building and using consensus engines in substrate.
//!
//! Much of this crate is _unstable_ and thus the API is likely to undergo
//! change. Implementors of traits should not rely on the interfaces to remain
//! the same.

// This provides "unused" building blocks to other crates
#![allow(dead_code)]

// our error-chain could potentially blow up otherwise
#![recursion_limit="128"]

#[macro_use] extern crate crossbeam_channel;
#[macro_use] extern crate log;

use std::sync::Arc;
use std::time::Duration;

use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::{AuthorityIdFor, Block};
use futures::prelude::*;
pub use inherents::InherentData;

pub mod offline_tracker;
pub mod error;
mod block_import;
mod select_chain;
pub mod import_queue;
pub mod evaluation;

// block size limit.
const MAX_BLOCK_SIZE: usize = 4 * 1024 * 1024 + 512;

pub use self::error::{Error, ErrorKind};
pub use block_import::{
	BlockImport, BlockOrigin, ForkChoiceStrategy, ImportedAux, ImportBlock, ImportResult, JustificationImport,
};
pub use select_chain::SelectChain;

/// Trait for getting the authorities at a given block.
pub trait Authorities<B: Block> {
	type Error: std::error::Error + Send + 'static;

	/// Get the authorities at the given block.
	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityIdFor<B>>, Self::Error>;
}

/// Environment producer for a Consensus instance. Creates proposer instance and communication streams.
pub trait Environment<B: Block> {
	/// The proposer type this creates.
	type Proposer: Proposer<B>;
	/// Error which can occur upon creation.
	type Error: From<Error>;

	/// Initialize the proposal logic on top of a specific header. Provide
	/// the authorities at that header.
	fn init(&self, parent_header: &B::Header, authorities: &[AuthorityIdFor<B>])
		-> Result<Self::Proposer, Self::Error>;
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
///
/// Proposers are generic over bits of "consensus data" which are engine-specific.
pub trait Proposer<B: Block> {
	/// Error type which can occur when proposing or evaluating.
	type Error: From<Error> + ::std::fmt::Debug + 'static;
	/// Future that resolves to a committed proposal.
	type Create: IntoFuture<Item=B, Error=Self::Error>;
	/// Create a proposal.
	fn propose(&self, inherent_data: InherentData, max_duration: Duration) -> Self::Create;
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
	fn is_major_syncing(&self) -> bool { false }
	fn is_offline(&self) -> bool { false }
}

impl<T: SyncOracle> SyncOracle for Arc<T> {
	fn is_major_syncing(&self) -> bool {
		T::is_major_syncing(&*self)
	}
	fn is_offline(&self) -> bool {
		T::is_offline(&*self)
	}
}

/// Extra verification for blocks.
pub trait ExtraVerification<B: Block>: Send + Sync {
	/// Future that resolves when the block is verified, or fails with error if
	/// not.
	type Verified: IntoFuture<Item=(),Error=String>;

	/// Do additional verification for this block.
	fn verify(
		&self,
		header: &B::Header,
		body: Option<&[B::Extrinsic]>,
	) -> Self::Verified;
}

/// A list of all well known keys in the cache.
pub mod well_known_cache_keys {
	/// The type representing cache keys.
	pub type Id = [u8; 4];

	/// A list of authorities.
	pub const AUTHORITIES: Id = *b"auth";
}
