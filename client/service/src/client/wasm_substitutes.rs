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

//! # WASM substitutes

use sc_client_api::backend;
use sc_executor::RuntimeVersionOf;
use sp_blockchain::{HeaderBackend, Result};
use sp_core::traits::{FetchRuntimeCode, RuntimeCode, WrappedRuntimeCode};
use sp_runtime::traits::{Block as BlockT, NumberFor};
use sp_state_machine::BasicExternalities;
use sp_version::RuntimeVersion;
use std::{
	collections::{hash_map::DefaultHasher, HashMap},
	hash::Hasher as _,
	sync::Arc,
};

/// A wasm substitute for the on chain wasm.
#[derive(Debug)]
struct WasmSubstitute<Block: BlockT> {
	code: Vec<u8>,
	hash: Vec<u8>,
	/// The block number on which we should start using the substitute.
	block_number: NumberFor<Block>,
	version: RuntimeVersion,
}

impl<Block: BlockT> WasmSubstitute<Block> {
	fn new(code: Vec<u8>, block_number: NumberFor<Block>, version: RuntimeVersion) -> Self {
		let hash = make_hash(&code);
		Self { code, hash, block_number, version }
	}

	fn runtime_code(&self, heap_pages: Option<u64>) -> RuntimeCode {
		RuntimeCode { code_fetcher: self, hash: self.hash.clone(), heap_pages }
	}

	/// Returns `true` when the substitute matches for the given `hash`.
	fn matches(
		&self,
		hash: <Block as BlockT>::Hash,
		backend: &impl backend::Backend<Block>,
	) -> bool {
		let requested_block_number = backend.blockchain().number(hash).ok().flatten();

		Some(self.block_number) <= requested_block_number
	}
}

/// Make a hash out of a byte string using the default rust hasher
fn make_hash<K: std::hash::Hash + ?Sized>(val: &K) -> Vec<u8> {
	let mut state = DefaultHasher::new();
	val.hash(&mut state);
	state.finish().to_le_bytes().to_vec()
}

impl<Block: BlockT> FetchRuntimeCode for WasmSubstitute<Block> {
	fn fetch_runtime_code(&self) -> Option<std::borrow::Cow<[u8]>> {
		Some(self.code.as_slice().into())
	}
}

#[derive(Debug, thiserror::Error)]
#[allow(missing_docs)]
pub enum WasmSubstituteError {
	#[error("Failed to get runtime version: {0}")]
	VersionInvalid(String),
}

impl From<WasmSubstituteError> for sp_blockchain::Error {
	fn from(err: WasmSubstituteError) -> Self {
		Self::Application(Box::new(err))
	}
}

/// Substitutes the on-chain wasm with some hard coded blobs.
#[derive(Debug)]
pub struct WasmSubstitutes<Block: BlockT, Executor, Backend> {
	/// spec_version -> WasmSubstitute
	substitutes: Arc<HashMap<u32, WasmSubstitute<Block>>>,
	executor: Executor,
	backend: Arc<Backend>,
}

impl<Block: BlockT, Executor: Clone, Backend> Clone for WasmSubstitutes<Block, Executor, Backend> {
	fn clone(&self) -> Self {
		Self {
			substitutes: self.substitutes.clone(),
			executor: self.executor.clone(),
			backend: self.backend.clone(),
		}
	}
}

impl<Executor, Backend, Block> WasmSubstitutes<Block, Executor, Backend>
where
	Executor: RuntimeVersionOf + Clone + 'static,
	Backend: backend::Backend<Block>,
	Block: BlockT,
{
	/// Create a new instance.
	pub fn new(
		substitutes: HashMap<NumberFor<Block>, Vec<u8>>,
		executor: Executor,
		backend: Arc<Backend>,
	) -> Result<Self> {
		let substitutes = substitutes
			.into_iter()
			.map(|(block_number, code)| {
				let runtime_code = RuntimeCode {
					code_fetcher: &WrappedRuntimeCode((&code).into()),
					heap_pages: None,
					hash: Vec::new(),
				};
				let version = Self::runtime_version(&executor, &runtime_code)?;
				let spec_version = version.spec_version;

				let substitute = WasmSubstitute::new(code, block_number, version);

				Ok((spec_version, substitute))
			})
			.collect::<Result<HashMap<_, _>>>()?;

		Ok(Self { executor, substitutes: Arc::new(substitutes), backend })
	}

	/// Get a substitute.
	///
	/// Returns `None` if there isn't any substitute required.
	pub fn get(
		&self,
		spec: u32,
		pages: Option<u64>,
		hash: Block::Hash,
	) -> Option<(RuntimeCode<'_>, RuntimeVersion)> {
		let s = self.substitutes.get(&spec)?;
		s.matches(hash, &*self.backend)
			.then(|| (s.runtime_code(pages), s.version.clone()))
	}

	fn runtime_version(executor: &Executor, code: &RuntimeCode) -> Result<RuntimeVersion> {
		let mut ext = BasicExternalities::default();
		executor
			.runtime_version(&mut ext, code)
			.map_err(|e| WasmSubstituteError::VersionInvalid(e.to_string()).into())
	}
}
