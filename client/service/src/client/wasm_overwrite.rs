// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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
use std::{ 
	fs, collections::{HashMap, hash_map::DefaultHasher}, path::Path,
	hash::Hasher as _, 
};
use codec::{Encode, Decode};
use sp_core::{
	traits::FetchRuntimeCode,
};
use sp_state_machine::{BasicExternalities, backend};
use sp_blockchain::Result;
use sc_executor::RuntimeInfo;
use sp_version::RuntimeVersion;
use sp_core::traits::RuntimeCode;
use hash_db::Hasher;

#[derive(Clone, Debug)]
struct WasmBlob {
	code: Vec<u8>,
}

impl WasmBlob {
	fn new(code: Vec<u8>) -> Self {
		Self { code }
	}

	fn runtime_code(&self, heap_pages: Option<u64>) -> RuntimeCode {
		RuntimeCode {
			code_fetcher: self,
			hash: make_hash(self.code.as_slice()).encode(),
			heap_pages,
		}
	}
}

/// Make a hash out of a byte string using the default rust hasher
pub fn make_hash<K: std::hash::Hash + ?Sized>(val: &K) -> Vec<u8> {
	let mut state = DefaultHasher::new();
	val.hash(&mut state);
	state.finish().to_le_bytes().to_vec()
}

impl FetchRuntimeCode for WasmBlob {
	fn fetch_runtime_code<'a>(&'a self) -> Option<std::borrow::Cow<'a, [u8]>> {
		Some(self.code.as_slice().into())
	}
}

#[derive(Clone, Debug)]
pub struct WasmOverwrite<E> {
	// Map of runtime spec version -> Wasm Blob
	overwrites: HashMap<u32, WasmBlob>,
	executor: E,
	enabled: bool,
}

impl<E> WasmOverwrite<E> 
where 
	E: RuntimeInfo + Clone + 'static 
{
	pub fn new<P>(path: P, enabled: bool, executor: E) -> Result<Self> 
	where
		P: AsRef<Path>,
	{
		let overwrites = Self::scrape_overwrites(path.as_ref(), &executor)?;
		Ok(Self { overwrites, executor, enabled })
	}
	
	/// Tries to replace the given `code` with an overwrite, if it exists.
	/// If the overwrite does not exist, or overwrites are not enabled,
	/// this function returns the original runtime code.
	pub fn try_replace<'a, 'b: 'a, B, H>(
		&'b self, 
		code: RuntimeCode<'a>, 
		state: &'a B,
	) -> Result<RuntimeCode<'a>>
	where
		B: backend::Backend<H>,
		H: Hasher
	{
		if !self.enabled {
			return Ok(code);
		}

		let backend_code = code.fetch_runtime_code()
			.ok_or(sp_blockchain::Error::Msg(format!("Runtime code could not be found in the backend")))?;
		let heap_pages = state.storage(sp_core::storage::well_known_keys::HEAP_PAGES)
			.ok()
			.flatten()
			.and_then(|d| Decode::decode(&mut &d[..]).ok()); 
		let version = Self::runtime_version(&self.executor, &WasmBlob::new(backend_code.to_vec()), heap_pages)?;
		
		self.overwrites
			.get(&version.spec_version)
			.map(|w| w.runtime_code(heap_pages))
			.map_or_else(|| Ok(code), Ok)
	}

	/// Scrapes a folder for WASM runtimes.
    /// Returns a hashmap of the runtime version and wasm runtime code.
	fn scrape_overwrites(dir: &Path, executor: &E) -> Result<HashMap<u32, WasmBlob>> {
		let handle_err = |e: std::io::Error | -> sp_blockchain::Error {
			sp_blockchain::Error::Msg(format!("{}", e.to_string()))
		};
		
		let mut overwrites = HashMap::new(); 
		if dir.is_dir() {
			for entry in fs::read_dir(dir).map_err(handle_err)? {
				let entry = entry.map_err(handle_err)?;
				let path = entry.path();
				let wasm = WasmBlob::new(fs::read(path).map_err(handle_err)?);
				let version = Self::runtime_version(executor, &wasm, Some(128))?;
				overwrites.insert(version.spec_version, wasm);
			}
		}
		Ok(overwrites)
	}

	fn runtime_version(executor: &E, code: &WasmBlob, heap_pages: Option<u64>) -> Result<RuntimeVersion> {
		let mut ext = BasicExternalities::default(); 
		executor.runtime_version(&mut ext, &code.runtime_code(heap_pages))
			.map_err(|e| sp_blockchain::Error::VersionInvalid(format!("{:?}", e)).into())
	}
}
