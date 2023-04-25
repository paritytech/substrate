// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate statement store API.

use codec::{Decode, Encode};
use jsonrpsee::core::{async_trait, RpcResult};
/// Re-export the API for backward compatibility.
pub use sc_rpc_api::statement::{error::Error, StatementApiServer};
use sc_rpc_api::DenyUnsafe;
use sp_core::Bytes;
use sp_statement_store::{StatementSource, SubmitResult};
use std::sync::Arc;

/// Statement store API
pub struct StatementStore {
	store: Arc<dyn sp_statement_store::StatementStore>,
	deny_unsafe: DenyUnsafe,
}

impl StatementStore {
	/// Create new instance of Offchain API.
	pub fn new(
		store: Arc<dyn sp_statement_store::StatementStore>,
		deny_unsafe: DenyUnsafe,
	) -> Self {
		StatementStore { store, deny_unsafe }
	}
}

#[async_trait]
impl StatementApiServer for StatementStore {
	fn dump(&self) -> RpcResult<Vec<Bytes>> {
		self.deny_unsafe.check_if_safe()?;

		let statements =
			self.store.statements().map_err(|e| Error::StatementStore(e.to_string()))?;
		Ok(statements.into_iter().map(|(_, s)| s.encode().into()).collect())
	}

	fn broadcasts(&self, match_all_topics: Vec<[u8; 32]>) -> RpcResult<Vec<Bytes>> {
		Ok(self
			.store
			.broadcasts(&match_all_topics)
			.map_err(|e| Error::StatementStore(e.to_string()))?
			.into_iter()
			.map(Into::into)
			.collect())
	}

	fn posted(&self, match_all_topics: Vec<[u8; 32]>, dest: [u8; 32]) -> RpcResult<Vec<Bytes>> {
		Ok(self
			.store
			.posted(&match_all_topics, dest)
			.map_err(|e| Error::StatementStore(e.to_string()))?
			.into_iter()
			.map(Into::into)
			.collect())
	}

	fn posted_clear(
		&self,
		match_all_topics: Vec<[u8; 32]>,
		dest: [u8; 32],
	) -> RpcResult<Vec<Bytes>> {
		Ok(self
			.store
			.posted_clear(&match_all_topics, dest)
			.map_err(|e| Error::StatementStore(e.to_string()))?
			.into_iter()
			.map(Into::into)
			.collect())
	}

	fn submit(&self, encoded: Bytes) -> RpcResult<()> {
		let statement = Decode::decode(&mut &*encoded)
			.map_err(|e| Error::StatementStore(format!("Eror decoding statement: {:?}", e)))?;
		match self.store.submit(statement, StatementSource::Local) {
			SubmitResult::New(_) | SubmitResult::Known => Ok(()),
			// `KnownExpired` should not happen. Expired statements submitted with
			// `StatementSource::Rpc` should be renewed.
			SubmitResult::KnownExpired =>
				Err(Error::StatementStore("Submitted an expired statement.".into()).into()),
			SubmitResult::Bad(e) => Err(Error::StatementStore(e.into()).into()),
			SubmitResult::Ignored => Err(Error::StatementStore("Store is full.".into()).into()),
			SubmitResult::InternalError(e) => Err(Error::StatementStore(e.to_string()).into()),
		}
	}

	fn remove(&self, hash: [u8; 32]) -> RpcResult<()> {
		Ok(self.store.remove(&hash).map_err(|e| Error::StatementStore(e.to_string()))?)
	}
}
