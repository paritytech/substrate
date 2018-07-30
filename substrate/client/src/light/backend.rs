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

//! Light client backend. Only stores headers and justifications of blocks.
//! Everything else is requested from full nodes on demand.

use std::sync::{Arc, Weak};

use primitives::AuthorityId;
use runtime_primitives::{bft::Justification, generic::BlockId};
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use state_machine::{Backend as StateBackend, TrieBackend as StateTrieBackend,
	TryIntoTrieBackend as TryIntoStateTrieBackend};

use backend::{Backend as ClientBackend, BlockImportOperation, RemoteBackend};
use blockchain::HeaderBackend as BlockchainHeaderBackend;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::fetcher::Fetcher;

/// Light client backend.
pub struct Backend<S, F> {
	blockchain: Arc<Blockchain<S, F>>,
}

/// Light block (header and justification) import operation.
pub struct ImportOperation<Block: BlockT, F> {
	is_new_best: bool,
	header: Option<Block::Header>,
	authorities: Option<Vec<AuthorityId>>,
	_phantom: ::std::marker::PhantomData<F>,
}

/// On-demand state.
pub struct OnDemandState<Block: BlockT, F> {
	fetcher: Weak<F>,
	block: Block::Hash,
}

impl<S, F> Backend<S, F> {
	/// Create new light backend.
	pub fn new(blockchain: Arc<Blockchain<S, F>>) -> Self {
		Self { blockchain }
	}

	/// Get shared blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}
}

impl<S, F, Block> ClientBackend<Block> for Backend<S, F> where Block: BlockT, S: BlockchainStorage<Block>, F: Fetcher<Block> {
	type BlockImportOperation = ImportOperation<Block, F>;
	type Blockchain = Blockchain<S, F>;
	type State = OnDemandState<Block, F>;

	fn begin_operation(&self, _block: BlockId<Block>) -> ClientResult<Self::BlockImportOperation> {
		Ok(ImportOperation {
			is_new_best: false,
			header: None,
			authorities: None,
			_phantom: Default::default(),
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> ClientResult<()> {
		let header = operation.header.expect("commit is called after set_block_data; set_block_data sets header; qed");
		self.blockchain.storage().import_header(operation.is_new_best, header, operation.authorities)
	}

	fn blockchain(&self) -> &Blockchain<S, F> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId<Block>) -> ClientResult<Self::State> {
		let block_hash = match block {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.blockchain.hash(n).unwrap_or_default(),
		};

		Ok(OnDemandState {
			block: block_hash.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", block)))?,
			fetcher: self.blockchain.fetcher(),
		})
	}

	fn revert(&self, _n: NumberFor<Block>) -> ClientResult<NumberFor<Block>> {
		unimplemented!()
	}
}

impl<S, F, Block> RemoteBackend<Block> for Backend<S, F> where Block: BlockT, S: BlockchainStorage<Block>, F: Fetcher<Block> {}

impl<F, Block> BlockImportOperation<Block> for ImportOperation<Block, F> where Block: BlockT, F: Fetcher<Block> {
	type State = OnDemandState<Block, F>;

	fn state(&self) -> ClientResult<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(
		&mut self,
		header: Block::Header,
		_body: Option<Vec<Block::Extrinsic>>,
		_justification: Option<Justification<Block::Hash>>,
		is_new_best: bool
	) -> ClientResult<()> {
		self.is_new_best = is_new_best;
		self.header = Some(header);
		Ok(())
	}

	fn update_authorities(&mut self, authorities: Vec<AuthorityId>) {
		self.authorities = Some(authorities);
	}

	fn update_storage(&mut self, _update: <Self::State as StateBackend>::Transaction) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, _iter: I) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}
}

impl<Block: BlockT, F> Clone for OnDemandState<Block, F> {
	fn clone(&self) -> Self {
		OnDemandState {
			fetcher: self.fetcher.clone(),
			block: self.block,
		}
	}
}

impl<Block, F> StateBackend for OnDemandState<Block, F> where Block: BlockT, F: Fetcher<Block> {
	type Error = ClientError;
	type Transaction = ();

	fn storage(&self, _key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		Err(ClientErrorKind::NotAvailableOnLightClient.into()) // TODO: fetch from remote node
	}

	fn for_keys_with_prefix<A: FnMut(&[u8])>(&self, _prefix: &[u8], _action: A) {
		// whole state is not available on light node
	}

	fn storage_root<I>(&self, _delta: I) -> ([u8; 32], Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)> {
		([0; 32], ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}
}

impl<Block, F> TryIntoStateTrieBackend for OnDemandState<Block, F> where Block: BlockT, F: Fetcher<Block> {
	fn try_into_trie_backend(self) -> Option<StateTrieBackend> {
		None
	}
}

#[cfg(test)]
pub mod tests {
	use futures::future::{ok, FutureResult};
	use parking_lot::Mutex;
	use call_executor::CallResult;
	use error::Error as ClientError;
	use test_client::runtime::{Hash, Block};
	use light::fetcher::{Fetcher, RemoteCallRequest};

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_call(&self, _request: RemoteCallRequest<Hash>) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}
	}
}
