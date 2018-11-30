// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Tracks offline validators.

// This provides "unused" building blocks to other crates
#![allow(dead_code)]

// our error-chain could potentially blow up otherwise
#![recursion_limit="128"]

extern crate substrate_primitives as primitives;
extern crate futures;
extern crate sr_version as runtime_version;
extern crate sr_primitives as runtime_primitives;
extern crate tokio;

extern crate parity_codec as codec;
#[macro_use]
extern crate parity_codec_derive;

#[macro_use]
extern crate error_chain;

use std::sync::Arc;

use primitives::{ed25519, AuthorityId};
use runtime_primitives::generic::BlockId;
use runtime_primitives::traits::Block;
use futures::prelude::*;

pub mod offline_tracker;
pub mod error;
mod block_import;
pub mod evaluation;

// block size limit.
const MAX_TRANSACTIONS_SIZE: usize = 4 * 1024 * 1024;

pub use self::error::{Error, ErrorKind};
pub use block_import::{BlockImport, ImportBlock, BlockOrigin, ImportResult};

/// Trait for getting the authorities at a given block.
pub trait Authorities<B: Block> {
	type Error: ::std::error::Error + Send + 'static;	/// Get the authorities at the given block.
	fn authorities(&self, at: &BlockId<B>) -> Result<Vec<AuthorityId>, Self::Error>;
}

/// Environment producer for a Consensus instance. Creates proposer instance and communication streams.
pub trait Environment<B: Block> {
	/// The proposer type this creates.
	type Proposer: Proposer<B>;
	/// Error which can occur upon creation.
	type Error: From<Error>;

	/// Initialize the proposal logic on top of a specific header. Provide
	/// the authorities at that header, and a local key to sign any additional
	/// consensus messages with as well.
	fn init(&self, parent_header: &B::Header, authorities: &[AuthorityId], sign_with: Arc<ed25519::Pair>)
		-> Result<Self::Proposer, Self::Error>;
}

/// Logic for a proposer.
///
/// This will encapsulate creation and evaluation of proposals at a specific
/// block.
pub trait Proposer<B: Block> {
	/// Error type which can occur when proposing or evaluating.
	type Error: From<Error> + ::std::fmt::Debug + 'static;
	/// Future that resolves to a committed proposal.
	type Create: IntoFuture<Item=B,Error=Self::Error>;
	/// Create a proposal.
	fn propose(&self) -> Self::Create;
}

/// An oracle for when major synchronization work is being undertaken.
///
/// Generally, consensus authoring work isn't undertaken while well behind
/// the head of the chain.
pub trait SyncOracle {
	/// Whether the synchronization service is undergoing major sync.
	/// Returns true if so.
	fn is_major_syncing(&self) -> bool;
}

/// A synchronization oracle for when there is no network.
#[derive(Clone, Copy, Debug)]
pub struct NoNetwork;

impl SyncOracle for NoNetwork {
	fn is_major_syncing(&self) -> bool { false }
}

impl<T: SyncOracle> SyncOracle for Arc<T> {
	fn is_major_syncing(&self) -> bool {
		T::is_major_syncing(&*self)
	}
}
