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

#![cfg_attr(not(feature = "std"), no_std)]

//! A crate which contains statement-store primitives.

use sp_std::vec::Vec;
use codec::{Decode, Encode};
use scale_info::TypeInfo;

pub type Topic = [u8; 32];
pub type DecryptionKey = [u8; 32];
pub type Hash = [u8; 32];
pub type BlockHash = [u8; 32];

#[cfg(feature = "std")]
pub use api::{StatementStore, SubmitResult, Error, Result};

/// Returns blake2-256 hash for the encoded statement.
#[cfg(feature = "std")]
pub fn hash_encoded(data: &[u8]) -> [u8; 32] {
	sp_core::hashing::blake2_256(data)
}

#[derive(Encode, Decode, TypeInfo, sp_runtime::RuntimeDebug, Clone, PartialEq, Eq)]
pub enum Proof {
	Sr25519 { signature: [u8; 64], signer: [u8; 32] },
	Ed25519 { signature: [u8; 64], signer: [u8; 32] },
	Secp256k1Ecdsa { signature: [u8; 65], signer: [u8; 33] },
	OnChain { who: [u8; 32], block_hash: BlockHash, event_index: u64 },
}

#[derive(Encode, Decode, TypeInfo, sp_runtime::RuntimeDebug, Clone, PartialEq, Eq)]
pub enum Field {
	AuthenticityProof(Proof),
	DecryptionKey(DecryptionKey),
	Priority(u32),
	Topic0(Topic),
	Topic1(Topic),
	Topic2(Topic),
	Topic3(Topic),
	Data(Vec<u8>),
}

#[derive(Encode, Decode, TypeInfo, sp_runtime::RuntimeDebug, Clone, PartialEq, Eq)]
pub struct Statement {
	fields: Vec<Field>,
}

impl Statement {
	pub fn new(proof: Proof) -> Statement {
		Statement {
			fields: sp_std::vec![Field::AuthenticityProof(proof)],
		}
	}

	#[cfg(feature = "std")]
	pub fn hash(&self) -> [u8; 32] {
		hash_encoded(&self.encode())
	}

	pub fn topic(&self, index: usize) -> Option<Topic> {
		for field in &self.fields {
			match (field, index) {
				(Field::Topic0(t), 0) => return Some(*t),
				(Field::Topic1(t), 1) => return Some(*t),
				(Field::Topic2(t), 2) => return Some(*t),
				(Field::Topic3(t), 3) => return Some(*t),
				_ => {},
			}
		}
		None
	}

	pub fn decryption_key(&self) -> Option<DecryptionKey> {
		for field in &self.fields {
			if let Field::DecryptionKey(key) = field {
				return Some(*key);
			}
		}
		None
	}

	pub fn into_data(self) -> Option<Vec<u8>> {
		for field in self.fields.into_iter() {
			if let Field::Data(data) = field {
				return Some(data);
			}
		}
		None
	}

	pub fn proof(&self) -> Option<&Proof> {
		if let Some(Field::AuthenticityProof(p)) = self.fields.get(0) {
			Some(p)
		} else {
			None
		}
	}

	/// Return encoded fields that can be signed to construct or verify a proof
	pub fn signature_material(&self) -> Vec<u8> {
		let mut out = Vec::new();
		let skip_fields = if let Some(Field::AuthenticityProof(_)) = self.fields.get(0) { 1 } else { 0 };
		for field in &self.fields[skip_fields..] {
			field.encode_to(&mut out)
		}
		out
	}

	/// Return a copy of this statement with proof removed
	pub fn strip_proof(&self) -> Statement {
		if let Some(Field::AuthenticityProof(_)) = self.fields.get(0) {
			return Statement { fields: self.fields[1..].iter().cloned().collect() }
		}
		self.clone()
	}
}

#[cfg(feature = "std")]
mod api {
	use crate::{Statement, Topic, Hash};
	use std::future::Future;

	#[derive(Debug, thiserror::Error)]
	pub enum Error {
		/// Database error.
		#[error("Database error: {0:?}")]
		Db(String),
		/// Error decoding statement structure.
		#[error("Error decoding statement: {0:?}")]
		Decode(String),
	}

	pub enum SubmitResult {
		OkNew(Hash),
		OkKnown(Hash),
		Bad(String),
		InternalError(Error),
	}

	pub type Result<T> = std::result::Result<T, Error>;

	pub trait StatementStore: Send + Sync {
		/// Return all statements, SCALE-encoded.
		fn dump_encoded(&self) -> Result<Vec<(Hash, Vec<u8>)>>;

		/// Return all statements.
		fn dump(&self) -> Result<Vec<(Hash, Statement)>>;

		/// Get statement by hash.
		fn statement(&self, hash: &Hash) -> Result<Option<Statement>>;

		/// Return the data of all known statements which include all topics and have no `DecryptionKey` field.
		fn broadcasts(&self, match_all_topics: &[Topic]) -> Result<Vec<Vec<u8>>>;

		/// Return the data of all known statements whose decryption key is identified as `dest` (this will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the private key for symmetric ciphers).
		fn posted(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>>;

		/// Return the decrypted data of all known statements whose decryption key is identified as `dest`. The key must be available to the client.
		fn posted_clear(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>>;

		/// Submit a statement.
		fn submit(&self, statement: Statement) -> SubmitResult;

		/// Submit a SCALE-encoded statement.
		fn submit_encoded(&self, statement: &[u8]) -> SubmitResult;

		fn submit_async(&self, statement: Statement) -> std::pin::Pin<Box<dyn Future<Output = SubmitResult> + Send>>;
	}
}

pub mod runtime_api {
	use codec::{Decode, Encode};
	use scale_info::TypeInfo;
	use sp_runtime::{RuntimeDebug};
	use crate::Statement;

	/// Information concerning a valid statement.
	#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
	pub struct ValidStatement {
		pub priority: u64,
		pub propagate: bool,
	}

	/// An invalid statement.
	#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug, TypeInfo)]
	pub enum InvalidStatement {
		Payment,
		BadProof,
		Stale,
		InternalError,
	}

	/// The source of the statement.
	///
	/// Depending on the source we might apply different validation schemes.
	#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
	pub enum StatementSource {
		/// Statement is coming from a local source, such as the OCW.
		Local,
		/// Statement has been received externally (network or RPC).
		External,
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
}
