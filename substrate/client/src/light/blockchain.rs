// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Light client blockchin backend. Only stores headers and justifications of recent
//! blocks. CHT roots are stored for headers of ancient blocks.

use std::sync::Weak;
use parking_lot::Mutex;

use primitives::AuthorityId;
use primitives::block::{Body, Header, HeaderHash, Id as BlockId, Number};
use primitives::bft::Justification;

use blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache,
	HeaderBackend as BlockchainHeaderBackend, Info as BlockchainInfo};
use error::Result as ClientResult;
use light::fetcher::Fetcher;

/// Light client blockchain storage.
pub trait Storage: BlockchainHeaderBackend {
	/// Store new header.
	fn import_header(&self, is_new_best: bool, header: Header, authorities: Option<Vec<AuthorityId>>) -> ClientResult<()>;

	/// Get CHT root for given block. Fails if the block is not pruned (not a part of any CHT).
	fn cht_root(&self, block: Number) -> ClientResult<HeaderHash>;

	/// Get storage cache.
	fn cache(&self) -> Option<&BlockchainCache>;
}

/// Light client blockchain.
pub struct Blockchain<S, F> {
	fetcher: Mutex<Weak<F>>,
	storage: S,
}

impl<S, F> Blockchain<S, F> where S: Storage {
	/// Create new light blockchain backed with given storage.
	pub fn new(storage: S) -> Self {
		Self {
			fetcher: Mutex::new(Default::default()),
			storage,
		}
	}

	/// Sets fetcher reference.
	pub fn set_fetcher(&self, fetcher: Weak<F>) {
		*self.fetcher.lock() = fetcher;
	}

	/// Get fetcher weak reference.
	pub fn fetcher(&self) -> Weak<F> {
		self.fetcher.lock().clone()
	}

	/// Get storage reference.
	pub fn storage(&self) -> &S {
		&self.storage
	}
}

impl<S, F> BlockchainHeaderBackend for Blockchain<S, F> where S: Storage, F: Fetcher {
	fn header(&self, id: BlockId) -> ClientResult<Option<Header>> {
		self.storage.header(id)
	}

	fn info(&self) -> ClientResult<BlockchainInfo> {
		self.storage.info()
	}

	fn status(&self, id: BlockId) -> ClientResult<BlockStatus> {
		self.storage.status(id)
	}

	fn hash(&self, number: Number) -> ClientResult<Option<HeaderHash>> {
		self.storage.hash(number)
	}
}

impl<S, F> BlockchainBackend for Blockchain<S, F> where S: Storage, F: Fetcher {
	fn body(&self, _id: BlockId) -> ClientResult<Option<Body>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, _id: BlockId) -> ClientResult<Option<Justification>> {
		Ok(None)
	}

	fn cache(&self) -> Option<&BlockchainCache> {
		self.storage.cache()
	}
}
