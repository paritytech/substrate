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

pub use crate::runtime_api::StatementSource;
use crate::{Hash, Statement, Topic};

/// Statement store error.
#[derive(Debug, Eq, PartialEq, thiserror::Error)]
pub enum Error {
	/// Database error.
	#[error("Database error: {0:?}")]
	Db(String),
	/// Error decoding statement structure.
	#[error("Error decoding statement: {0:?}")]
	Decode(String),
	/// Error making runtime call.
	#[error("Error calling into the runtime")]
	Runtime,
}

#[derive(Debug, PartialEq, Eq)]
/// Network propagation priority.
pub enum NetworkPriority {
	/// High priority. Statement should be broadcast to all peers.
	High,
	/// Low priority.
	Low,
}

/// Statement submission outcome
#[derive(Debug, Eq, PartialEq)]
pub enum SubmitResult {
	/// Accepted as new with given score
	New(NetworkPriority),
	/// Known statement
	Known,
	/// Known statement that's already expired.
	KnownExpired,
	/// Priority is too low or the size is too big.
	Ignored,
	/// Statement failed validation.
	Bad(&'static str),
	/// Internal store error.
	InternalError(Error),
}

/// Result type for `Error`
pub type Result<T> = std::result::Result<T, Error>;

/// Statement store API.
pub trait StatementStore: Send + Sync {
	/// Return all statements.
	fn statements(&self) -> Result<Vec<(Hash, Statement)>>;

	/// Get statement by hash.
	fn statement(&self, hash: &Hash) -> Result<Option<Statement>>;

	/// Return the data of all known statements which include all topics and have no `DecryptionKey`
	/// field.
	fn broadcasts(&self, match_all_topics: &[Topic]) -> Result<Vec<Vec<u8>>>;

	/// Return the data of all known statements whose decryption key is identified as `dest` (this
	/// will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the
	/// private key for symmetric ciphers).
	fn posted(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>>;

	/// Return the decrypted data of all known statements whose decryption key is identified as
	/// `dest`. The key must be available to the client.
	fn posted_clear(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>>;

	/// Submit a statement.
	fn submit(&self, statement: Statement, source: StatementSource) -> SubmitResult;

	/// Remove a statement from the store.
	fn remove(&self, hash: &Hash) -> Result<()>;
}
