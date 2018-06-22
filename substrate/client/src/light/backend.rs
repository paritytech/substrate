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
use futures::{IntoFuture, Future};

use primitives::AuthorityId;
use runtime_primitives::{bft::Justification, generic::BlockId};
use runtime_primitives::traits::Block as BlockT;
use state_machine::{Backend as StateBackend, TrieBackend as StateTrieBackend,
	TryIntoTrieBackend as TryIntoStateTrieBackend};

use backend::{Backend as ClientBackend, BlockImportOperation, RemoteBackend};
use blockchain::HeaderBackend as BlockchainHeaderBackend;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::fetcher::{Fetcher, RemoteReadRequest};

/// Light client backend.
pub struct Backend<S, F> {
	blockchain: Arc<Blockchain<S, F>>,
}

/// Ligh block (header and justification) import operation.
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

/*impl<S, F, Block> Backend<S, F> where Block: BlockT, S: BlockchainStorage<Block>, F: Fetcher<Block> {
	fn id(&self, id: BlockId<Block>) -> Option<Block::Hash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.blockchain.hash(n).unwrap_or_default(),
		}
	}
}
*/
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

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		self.fetcher.upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				key: key.to_vec(),
				retry_count: None,
			})
			.into_future().wait()
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
	use futures::future::{ok, err, FutureResult};
	use parking_lot::Mutex;
	use call_executor::CallResult;
	use executor;
	use error::Error as ClientError;
	use test_client;
	use test_client::runtime::{Hash, Header, Block};
	use in_mem::{Blockchain as InMemoryBlockchain};
	use light::{new_fetch_checker, new_light_blockchain};
	use light::fetcher::{Fetcher, FetchChecker, LightDataChecker, RemoteHeaderRequest, RemoteCallRequest};
	//use runtime_primitives::testing::{H256 as Hash, Header, Block as RawBlock};
	use super::*;

	//type Block = RawBlock<u64>;
	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteHeaderResult = FutureResult<Header, ClientError>;
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_header(&self, _request: RemoteHeaderRequest<u64>) -> Self::RemoteHeaderResult {
			err("Not implemented on test node".into())
		}

		fn remote_read(&self, _request: RemoteReadRequest<Hash>) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest<Hash>) -> Self::RemoteCallResult {
			ok((*self.lock()).clone())
		}
	}

	#[test]
	fn storage_read_proof_is_generated_and_checked() {
		// prepare remote client
		let remote_client = test_client::new();
		let remote_block_id = BlockId::Number(0);
		let remote_block_hash = remote_client.block_hash(0).unwrap().unwrap();
		let mut remote_block_header = remote_client.header(&remote_block_id).unwrap().unwrap();
		remote_block_header.state_root = remote_client.state_at(&remote_block_id).unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.authorities_at(&remote_block_id).unwrap().len();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, b":auth:len").unwrap();

		// check remote read proof locally
		let local_storage = InMemoryBlockchain::<Block>::new();
		local_storage.insert(remote_block_hash, remote_block_header, None, None, true);
		let local_executor = test_client::NativeExecutor::new();
		let local_checker: LightDataChecker<InMemoryBlockchain<Block>, executor::NativeExecutor<test_client::NativeExecutor>, OkCallFetcher> =
			new_fetch_checker(new_light_blockchain(local_storage), local_executor);
		assert_eq!(local_checker.check_read_proof(&RemoteReadRequest {
			block: remote_block_hash,
			key: b":auth:len".to_vec(),
			retry_count: None,
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}
}
