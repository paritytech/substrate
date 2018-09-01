// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Light client backend. Only stores headers and justifications of blocks.
//! Everything else is requested from full nodes on demand.

use std::sync::{Arc, Weak};
use futures::{Future, IntoFuture};
use parking_lot::RwLock;

use primitives::AuthorityId;
use runtime_primitives::{bft::Justification, generic::BlockId};
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use state_machine::{
	Backend as StateBackend,
	TrieBackend as StateTrieBackend,
	TryIntoTrieBackend as TryIntoStateTrieBackend
};

use backend::{Backend as ClientBackend, BlockImportOperation, RemoteBackend};
use blockchain::HeaderBackend as BlockchainHeaderBackend;
use error::{Error as ClientError, ErrorKind as ClientErrorKind, Result as ClientResult};
use light::blockchain::{Blockchain, Storage as BlockchainStorage};
use light::fetcher::{Fetcher, RemoteReadRequest};
use patricia_trie::NodeCodec;
use hashdb::Hasher;

/// Light client backend.
pub struct Backend<S, F> {
	blockchain: Arc<Blockchain<S, F>>,
}

/// Light block (header and justification) import operation.
pub struct ImportOperation<Block: BlockT, S, F> {
	is_new_best: bool,
	header: Option<Block::Header>,
	authorities: Option<Vec<AuthorityId>>,
	_phantom: ::std::marker::PhantomData<(S, F)>,
}

/// On-demand state.
pub struct OnDemandState<Block: BlockT, S, F> {
	fetcher: Weak<F>,
	blockchain: Weak<Blockchain<S, F>>,
	block: Block::Hash,
	cached_header: RwLock<Option<Block::Header>>,
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

impl<S, F, Block, H, C> ClientBackend<Block, H, C> for Backend<S, F> where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher,
	C: NodeCodec<H>,
{
	type BlockImportOperation = ImportOperation<Block, S, F>;
	type Blockchain = Blockchain<S, F>;
	type State = OnDemandState<Block, S, F>;

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
			fetcher: self.blockchain.fetcher(),
			blockchain: Arc::downgrade(&self.blockchain),
			block: block_hash.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", block)))?,
			cached_header: RwLock::new(None),
		})
	}

	fn revert(&self, _n: NumberFor<Block>) -> ClientResult<NumberFor<Block>> {
		unimplemented!()
	}
}

impl<S, F, Block, H, C> RemoteBackend<Block, H, C> for Backend<S, F>
where
	Block: BlockT,
	S: BlockchainStorage<Block>,
	F: Fetcher<Block>,
	H: Hasher,
	C: NodeCodec<H>,
{}

impl<S, F, Block, H, C> BlockImportOperation<Block, H, C> for ImportOperation<Block, S, F>
where
	Block: BlockT,
	F: Fetcher<Block>,
	S: BlockchainStorage<Block>,
	H: Hasher,
	C: NodeCodec<H>,
{
	type State = OnDemandState<Block, S, F>;

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

	fn update_storage(&mut self, _update: <Self::State as StateBackend<H, C>>::Transaction) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}

	fn reset_storage<I: Iterator<Item=(Vec<u8>, Vec<u8>)>>(&mut self, _iter: I) -> ClientResult<()> {
		// we're not storing anything locally => ignore changes
		Ok(())
	}
}

impl<Block, S, F, H, C> StateBackend<H, C> for OnDemandState<Block, S, F>
	where
		Block: BlockT,
		S: BlockchainStorage<Block>,
		F: Fetcher<Block>,
		H: Hasher,
		C: NodeCodec<H>,
{
	type Error = ClientError;
	type Transaction = ();

	fn storage(&self, key: &[u8]) -> ClientResult<Option<Vec<u8>>> {
		let mut header = self.cached_header.read().clone();
		if header.is_none() {
			let cached_header = self.blockchain.upgrade()
				.ok_or_else(|| ClientErrorKind::UnknownBlock(format!("{}", self.block)).into())
				.and_then(|blockchain| blockchain.expect_header(BlockId::Hash(self.block)))?;
			header = Some(cached_header.clone());
			*self.cached_header.write() = Some(cached_header);
		}

		self.fetcher.upgrade().ok_or(ClientErrorKind::NotAvailableOnLightClient)?
			.remote_read(RemoteReadRequest {
				block: self.block,
				header: header.expect("if block above guarantees that header is_some(); qed"),
				key: key.to_vec(),
			})
			.into_future().wait()
	}

	fn for_keys_with_prefix<A: FnMut(&[u8])>(&self, _prefix: &[u8], _action: A) {
		// whole state is not available on light node
	}

	fn storage_root<I>(&self, _delta: I) -> (H::Out, Self::Transaction)
		where I: IntoIterator<Item=(Vec<u8>, Option<Vec<u8>>)> {
		(H::Out::default(), ())
	}

	fn pairs(&self) -> Vec<(Vec<u8>, Vec<u8>)> {
		// whole state is not available on light node
		Vec::new()
	}
}

impl<Block, S, F, H, C> TryIntoStateTrieBackend<H, C> for OnDemandState<Block, S, F>
where
	Block: BlockT,
	F: Fetcher<Block>,
	H: Hasher,
	C: NodeCodec<H>,
{
	fn try_into_trie_backend(self) -> Option<StateTrieBackend<H, C>> {
		None
	}
}

#[cfg(test)]
pub mod tests {
	use futures::future::{ok, err, FutureResult};
	use parking_lot::Mutex;
	use call_executor::CallResult;
	use executor::NativeExecutionDispatch;
	use error::Error as ClientError;
	use test_client::{self, runtime::{Header, Block}};
	use light::new_fetch_checker;
	use light::fetcher::{Fetcher, FetchChecker, RemoteCallRequest};
	use super::*;
	use primitives::{KeccakHasher, RlpCodec};

	pub type OkCallFetcher = Mutex<CallResult>;

	impl Fetcher<Block> for OkCallFetcher {
		type RemoteReadResult = FutureResult<Option<Vec<u8>>, ClientError>;
		type RemoteCallResult = FutureResult<CallResult, ClientError>;

		fn remote_read(&self, _request: RemoteReadRequest<Header>) -> Self::RemoteReadResult {
			err("Not implemented on test node".into())
		}

		fn remote_call(&self, _request: RemoteCallRequest<Header>) -> Self::RemoteCallResult {
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
		remote_block_header.state_root = remote_client.state_at(&remote_block_id)
			.unwrap().storage_root(::std::iter::empty()).0.into();

		// 'fetch' read proof from remote node
		let authorities_len = remote_client.authorities_at(&remote_block_id).unwrap().len();
		let remote_read_proof = remote_client.read_proof(&remote_block_id, b":auth:len").unwrap();

		// check remote read proof locally
		let local_executor = test_client::LocalExecutor::new();
		let local_checker = new_fetch_checker::<_, KeccakHasher, RlpCodec>(local_executor);
		let request = RemoteReadRequest {
			block: remote_block_hash,
			header: remote_block_header,
			key: b":auth:len".to_vec(),
		};
		assert_eq!((&local_checker as &FetchChecker<Block>).check_read_proof(
			&request,
			remote_read_proof).unwrap().unwrap()[0], authorities_len as u8);
	}
}
