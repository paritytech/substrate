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
use primitives::block::{Body, Header, HeaderHash, Id as BlockId};
use primitives::bft::Justification;
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
pub struct ImportOperation<F> {
	is_new_best: bool,
	header: Option<Header>,
	authorities: Option<Vec<AuthorityId>>,
	_phantom: ::std::marker::PhantomData<F>,
}

/// On-demand state.
pub struct OnDemandState<F> {
	fetcher: Weak<F>,
	block: HeaderHash,
}

impl<S, F> Backend<S, F> where S: BlockchainStorage, F: Fetcher {
	/// Create new light backend.
	pub fn new(blockchain: Arc<Blockchain<S, F>>) -> Self {
		Self { blockchain }
	}

	/// Get shared blockchain reference.
	pub fn blockchain(&self) -> &Arc<Blockchain<S, F>> {
		&self.blockchain
	}

	fn id(&self, id: BlockId) -> Option<HeaderHash> {
		match id {
			BlockId::Hash(h) => Some(h),
			BlockId::Number(n) => self.blockchain.hash(n).unwrap_or_default(),
		}
	}
}

impl<S, F> ClientBackend for Backend<S, F> where S: BlockchainStorage, F: Fetcher {
	type BlockImportOperation = ImportOperation<F>;
	type Blockchain = Blockchain<S, F>;
	type State = OnDemandState<F>;

	fn begin_operation(&self, _block: BlockId) -> ClientResult<Self::BlockImportOperation> {
		Ok(ImportOperation {
			is_new_best: false,
			header: None,
			authorities: None,
			_phantom: Default::default(),
		})
	}

	fn commit_operation(&self, operation: Self::BlockImportOperation) -> ClientResult<()> {
		let header = operation.header.expect("commit is called after set_block_data; set_block_data sets header; qed");
		self.blockchain.import_header(operation.is_new_best, header, operation.authorities)
	}

	fn blockchain(&self) -> &Blockchain<S, F> {
		&self.blockchain
	}

	fn state_at(&self, block: BlockId) -> ClientResult<Self::State> {
		Ok(OnDemandState {
			block: self.id(block).ok_or(ClientErrorKind::UnknownBlock(block))?,
			fetcher: self.blockchain.fetcher(),
		})
	}
}

impl<S, F> RemoteBackend for Backend<S, F> where S: BlockchainStorage, F: Fetcher {}

impl<F> BlockImportOperation for ImportOperation<F> where F: Fetcher {
	type State = OnDemandState<F>;

	fn state(&self) -> ClientResult<Option<&Self::State>> {
		// None means 'locally-stateless' backend
		Ok(None)
	}

	fn set_block_data(&mut self, header: Header, _body: Option<Body>, _justification: Option<Justification>, is_new_best: bool) -> ClientResult<()> {
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

impl<F> Clone for OnDemandState<F> {
	fn clone(&self) -> Self {
		OnDemandState {
			fetcher: self.fetcher.clone(),
			block: self.block,
		}
	}
}

impl<F> StateBackend for OnDemandState<F> where F: Fetcher {
	type Error = ClientError;
	type Transaction = ();

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		self.fetcher.upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				key: key.to_vec(),
				..Default::default()
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

impl<F> TryIntoStateTrieBackend for OnDemandState<F> where F: Fetcher {
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
	use in_mem::{Blockchain as InMemoryBlockchain};
	use light::{new_fetch_checker, new_light_blockchain};
	use light::fetcher::{Fetcher, FetchChecker, LightDataChecker, RemoteCallRequest};
	use super::*;

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher for OkCallFetcher {
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_read(&self, _request: RemoteReadRequest) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest) -> Self::RemoteCallResult {
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
		let local_storage = InMemoryBlockchain::new();
		local_storage.insert(remote_block_hash, remote_block_header, None, None, true);
		let local_executor = test_client::NativeExecutor::new();
		let local_checker: LightDataChecker<InMemoryBlockchain, executor::NativeExecutor<test_client::NativeExecutor>, OkCallFetcher> =
			new_fetch_checker(new_light_blockchain(local_storage), local_executor);
		assert_eq!(local_checker.check_read_proof(&RemoteReadRequest {
			block: remote_block_hash,
			key: b":auth:len".to_vec(),
			..Default::default()
		}, remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}
}
