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

use primitives::block::{Body, Header, HeaderHash, Id as BlockId, Number};
use primitives::bft::Justification;

use backend::Backend as ClientBackend;
use blockchain::{Backend as BlockchainBackend, BlockStatus, Cache as BlockchainCache, Info as BlockchainInfo};
use error::Result as ClientResult;
use light::fetcher::Fetcher;

/// Light client blockchain.
pub struct Blockchain<B, F> {
	fetcher: Mutex<Weak<F>>,
	storage: B,
}

impl<B, F> Blockchain<B, F> {
	/// Create new light blockchain.
	pub fn new(storage: B) -> Self {
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
	pub fn storage(&self) -> &B {
		&self.storage
	}
}

impl<B, F> BlockchainBackend for Blockchain<B, F> where B: ClientBackend, F: Fetcher {
	fn header(&self, id: BlockId) -> ClientResult<Option<Header>> {
		self.storage.blockchain().header(id)
	}

	fn body(&self, _id: BlockId) -> ClientResult<Option<Body>> {
		// TODO [light]: fetch from remote node
		Ok(None)
	}

	fn justification(&self, id: BlockId) -> ClientResult<Option<Justification>> {
		self.storage.blockchain().justification(id)
	}

	fn info(&self) -> ClientResult<BlockchainInfo> {
		self.storage.blockchain().info()
	}

	fn status(&self, id: BlockId) -> ClientResult<BlockStatus> {
		self.storage.blockchain().status(id)
	}

	fn hash(&self, number: Number) -> ClientResult<Option<HeaderHash>> {
		self.storage.blockchain().hash(number)
	}

	fn cache(&self) -> Option<&BlockchainCache> {
		self.storage.blockchain().cache()
	}
}
