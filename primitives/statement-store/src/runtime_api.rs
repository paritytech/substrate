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

//! Runtime support for the statement store.

use crate::{Topic, Statement, Hash};
use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;
use sp_runtime_interface::{runtime_interface, pass_by::PassByEnum};
use sp_externalities::ExternalitiesExt;
use sp_std::vec::Vec;

/// Information concerning a valid statement.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ValidStatement {
	/// Statement priority as calculated by the runtime. Higher priority statements have lower
	/// chance of being evicted.
	pub priority: u64,
}

/// An reason for an invalid statement.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug, TypeInfo)]
pub enum InvalidStatement {
	/// Failed proof validation.
	BadProof,
	/// Missing proof.
	NoProof,
	/// Validity could not be checked because of internal error.
	InternalError,
}

/// The source of the statement.
///
/// Depending on the source we might apply different validation schemes.
#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum StatementSource {
	/// Statement is coming from the on-chain worker.
	Chain,
	/// Statement has been received from the gossip network.
	Network,
	/// Statement has been submitted over the RPC api.
	Rpc,
}

impl StatementSource {
	/// Check if the source allows the statement to be resubmitted to the store, extending its
	/// expiration date.
	pub fn can_be_resubmitted(&self) -> bool {
		match self {
			StatementSource::Chain | StatementSource::Rpc => true,
			StatementSource::Network => false,
		}
	}
}

sp_api::decl_runtime_apis! {
	/// Runtime API trait for statement validation.
	pub trait ValidateStatement {
		/// Validate the statement.
		fn validate_statement(
			source: StatementSource,
			statement: Statement,
		) -> Result<ValidStatement, InvalidStatement>;
	}
}

#[cfg(feature = "std")]
sp_externalities::decl_extension! {
	/// The offchain database extension that will be registered at the Substrate externalities.
	pub struct StatementStoreExt(std::sync::Arc<dyn crate::StatementStore>);
}

#[cfg(feature = "std")]
/// Host extensions for the runtime.
impl StatementStoreExt {
	/// Create new instance of externalities extensions.
	pub fn new(store: std::sync::Arc<dyn crate::StatementStore>) -> Self {
		Self(store)
	}
}

#[derive(Debug, Eq, PartialEq, Clone, Copy, Encode, Decode, PassByEnum)]
/// Submission result.
pub enum SubmitResult {
	/// Accepted as new.
	OkNew,
	/// Known statement
	OkKnown,
	/// Statement failed validation.
	Bad,
	/// The store is not available.
	NotAvailable,
}

/// Export functions for the WASM host.
#[cfg(feature = "std")]
pub type HostFunctions = (
	io::HostFunctions,
);

/// Host interface
#[runtime_interface]
pub trait Io {
	/// Submit a new new statement. The statement will be broadcast to the network.
	/// This is meant to be used by the offchain worker.
	fn submit_statement(&mut self, statement: Statement) -> SubmitResult  {
		if let Some(StatementStoreExt(store)) = self.extension::<StatementStoreExt>() {
			match store.submit(statement, StatementSource::Chain) {
				crate::SubmitResult::New(_) => SubmitResult::OkNew,
				crate::SubmitResult::Known => SubmitResult::OkKnown,
				// This should not happen for `StatementSource::Chain`. An existing statement will be
				// overwritten.
				crate::SubmitResult::KnownExpired => SubmitResult::Bad,
				crate::SubmitResult::Bad(_) => SubmitResult::Bad,
				crate::SubmitResult::InternalError(_) => SubmitResult::Bad,
			}
		} else {
			SubmitResult::NotAvailable
		}
	}

	/// Return all statements.
	fn dump(&mut self) -> Vec<(Hash, Statement)> {
		if let Some(StatementStoreExt(store)) = self.extension::<StatementStoreExt>() {
			store.dump().unwrap_or_default()
		} else {
			Vec::default()
		}
	}

	/// Return the data of all known statements which include all topics and have no `DecryptionKey`
	/// field.
	fn broadcasts(&mut self, match_all_topics: &[Topic]) -> Vec<Vec<u8>> {
		if let Some(StatementStoreExt(store)) = self.extension::<StatementStoreExt>() {
			store.broadcasts(match_all_topics).unwrap_or_default()
		} else {
			Vec::default()
		}
	}

	/// Return the data of all known statements whose decryption key is identified as `dest` (this
	/// will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the
	/// private key for symmetric ciphers).
	fn posted(&mut self, match_all_topics: &[Topic], dest: [u8; 32]) -> Vec<Vec<u8>> {
		if let Some(StatementStoreExt(store)) = self.extension::<StatementStoreExt>() {
			store.posted(match_all_topics, dest).unwrap_or_default()
		} else {
			Vec::default()
		}
	}

	/// Return the decrypted data of all known statements whose decryption key is identified as
	/// `dest`. The key must be available to the client.
	fn posted_clear(&mut self, match_all_topics: &[Topic], dest: [u8; 32]) -> Vec<Vec<u8>> {
		if let Some(StatementStoreExt(store)) = self.extension::<StatementStoreExt>() {
			store.posted_clear(match_all_topics, dest).unwrap_or_default()
		} else {
			Vec::default()
		}
	}
}
