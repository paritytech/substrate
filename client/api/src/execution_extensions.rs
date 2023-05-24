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

//! Execution extensions for runtime calls.
//!
//! This module is responsible for defining the execution
//! strategy for the runtime calls and provide the right `Externalities`
//! extensions to support APIs for particular execution context & capabilities.

use codec::Decode;
use parking_lot::RwLock;
use sc_transaction_pool_api::OffchainSubmitTransaction;
use sp_core::{
	offchain::{self, OffchainDbExt, OffchainWorkerExt, TransactionPoolExt},
	traits::{ReadRuntimeVersion, ReadRuntimeVersionExt},
	ExecutionContext,
};
use sp_externalities::{Extension, Extensions};
use sp_keystore::{KeystoreExt, KeystorePtr};
use sp_runtime::{
	generic::BlockId,
	traits::{Block as BlockT, NumberFor},
};
pub use sp_state_machine::ExecutionStrategy;
use sp_state_machine::{DefaultHandler, ExecutionManager};
use std::{
	marker::PhantomData,
	sync::{Arc, Weak},
};

/// Execution strategies settings.
#[derive(Debug, Clone)]
pub struct ExecutionStrategies {
	/// Execution strategy used when syncing.
	pub syncing: ExecutionStrategy,
	/// Execution strategy used when importing blocks.
	pub importing: ExecutionStrategy,
	/// Execution strategy used when constructing blocks.
	pub block_construction: ExecutionStrategy,
	/// Execution strategy used for offchain workers.
	pub offchain_worker: ExecutionStrategy,
	/// Execution strategy used in other cases.
	pub other: ExecutionStrategy,
}

impl Default for ExecutionStrategies {
	fn default() -> ExecutionStrategies {
		ExecutionStrategies {
			syncing: ExecutionStrategy::NativeElseWasm,
			importing: ExecutionStrategy::NativeElseWasm,
			block_construction: ExecutionStrategy::AlwaysWasm,
			offchain_worker: ExecutionStrategy::NativeWhenPossible,
			other: ExecutionStrategy::NativeElseWasm,
		}
	}
}

/// Generate the starting set of [`Extensions`].
///
/// These [`Extensions`] are passed to the environment a runtime is executed in.
pub trait ExtensionsFactory<Block: BlockT>: Send + Sync {
	/// Create [`Extensions`] for the given input.
	///
	/// - `block_hash`: The hash of the block in the context that extensions will be used.
	/// - `block_number`: The number of the block in the context that extensions will be used.
	/// - `capabilities`: The capabilities
	fn extensions_for(
		&self,
		block_hash: Block::Hash,
		block_number: NumberFor<Block>,
		capabilities: offchain::Capabilities,
	) -> Extensions;
}

impl<Block: BlockT> ExtensionsFactory<Block> for () {
	fn extensions_for(
		&self,
		_: Block::Hash,
		_: NumberFor<Block>,
		_capabilities: offchain::Capabilities,
	) -> Extensions {
		Extensions::new()
	}
}

impl<Block: BlockT, T: ExtensionsFactory<Block>> ExtensionsFactory<Block> for Vec<T> {
	fn extensions_for(
		&self,
		block_hash: Block::Hash,
		block_number: NumberFor<Block>,
		capabilities: offchain::Capabilities,
	) -> Extensions {
		let mut exts = Extensions::new();
		exts.extend(self.iter().map(|e| e.extensions_for(block_hash, block_number, capabilities)));
		exts
	}
}

/// An [`ExtensionsFactory`] that registers an [`Extension`] before a certain block.
pub struct ExtensionBeforeBlock<Block: BlockT, Ext> {
	before: NumberFor<Block>,
	_marker: PhantomData<fn(Ext) -> Ext>,
}

impl<Block: BlockT, Ext> ExtensionBeforeBlock<Block, Ext> {
	/// Create the extension factory.
	///
	/// - `before`: The block number until the extension should be registered.
	pub fn new(before: NumberFor<Block>) -> Self {
		Self { before, _marker: PhantomData }
	}
}

impl<Block: BlockT, Ext: Default + Extension> ExtensionsFactory<Block>
	for ExtensionBeforeBlock<Block, Ext>
{
	fn extensions_for(
		&self,
		_: Block::Hash,
		block_number: NumberFor<Block>,
		_: offchain::Capabilities,
	) -> Extensions {
		let mut exts = Extensions::new();

		if block_number < self.before {
			exts.register(Ext::default());
		}

		exts
	}
}

/// Create a Offchain DB accessor object.
pub trait DbExternalitiesFactory: Send + Sync {
	/// Create [`offchain::DbExternalities`] instance.
	fn create(&self) -> Box<dyn offchain::DbExternalities>;
}

impl<T: offchain::DbExternalities + Clone + Sync + Send + 'static> DbExternalitiesFactory for T {
	fn create(&self) -> Box<dyn offchain::DbExternalities> {
		Box::new(self.clone())
	}
}

/// A producer of execution extensions for offchain calls.
///
/// This crate aggregates extensions available for the offchain calls
/// and is responsible for producing a correct `Extensions` object.
/// for each call, based on required `Capabilities`.
pub struct ExecutionExtensions<Block: BlockT> {
	strategies: ExecutionStrategies,
	keystore: Option<KeystorePtr>,
	offchain_db: Option<Box<dyn DbExternalitiesFactory>>,
	// FIXME: these three are only RwLock because of https://github.com/paritytech/substrate/issues/4587
	//        remove when fixed.
	// To break retain cycle between `Client` and `TransactionPool` we require this
	// extension to be a `Weak` reference.
	// That's also the reason why it's being registered lazily instead of
	// during initialization.
	transaction_pool: RwLock<Option<Weak<dyn OffchainSubmitTransaction<Block>>>>,
	extensions_factory: RwLock<Box<dyn ExtensionsFactory<Block>>>,
	statement_store: RwLock<Option<Weak<dyn sp_statement_store::StatementStore>>>,
	read_runtime_version: Arc<dyn ReadRuntimeVersion>,
}

impl<Block: BlockT> ExecutionExtensions<Block> {
	/// Create new `ExecutionExtensions` given a `keystore` and `ExecutionStrategies`.
	pub fn new(
		strategies: ExecutionStrategies,
		keystore: Option<KeystorePtr>,
		offchain_db: Option<Box<dyn DbExternalitiesFactory>>,
		read_runtime_version: Arc<dyn ReadRuntimeVersion>,
	) -> Self {
		let transaction_pool = RwLock::new(None);
		let statement_store = RwLock::new(None);
		let extensions_factory = Box::new(());
		Self {
			strategies,
			keystore,
			offchain_db,
			extensions_factory: RwLock::new(extensions_factory),
			transaction_pool,
			statement_store,
			read_runtime_version,
		}
	}

	/// Get a reference to the execution strategies.
	pub fn strategies(&self) -> &ExecutionStrategies {
		&self.strategies
	}

	/// Set the new extensions_factory
	pub fn set_extensions_factory(&self, maker: impl ExtensionsFactory<Block> + 'static) {
		*self.extensions_factory.write() = Box::new(maker);
	}

	/// Register transaction pool extension.
	pub fn register_transaction_pool<T>(&self, pool: &Arc<T>)
	where
		T: OffchainSubmitTransaction<Block> + 'static,
	{
		*self.transaction_pool.write() = Some(Arc::downgrade(pool) as _);
	}

	/// Register statement store extension.
	pub fn register_statement_store(&self, store: Arc<dyn sp_statement_store::StatementStore>) {
		*self.statement_store.write() = Some(Arc::downgrade(&store) as _);
	}

	/// Based on the execution context and capabilities it produces
	/// the extensions object to support desired set of APIs.
	pub fn extensions(
		&self,
		block_hash: Block::Hash,
		block_number: NumberFor<Block>,
		context: ExecutionContext,
	) -> Extensions {
		let capabilities = context.capabilities();

		let mut extensions =
			self.extensions_factory
				.read()
				.extensions_for(block_hash, block_number, capabilities);

		if capabilities.contains(offchain::Capabilities::KEYSTORE) {
			if let Some(ref keystore) = self.keystore {
				extensions.register(KeystoreExt(keystore.clone()));
			}
		}

		if capabilities.contains(offchain::Capabilities::TRANSACTION_POOL) {
			if let Some(pool) = self.transaction_pool.read().as_ref().and_then(|x| x.upgrade()) {
				extensions.register(TransactionPoolExt(Box::new(TransactionPoolAdapter {
					at: BlockId::Hash(block_hash),
					pool,
				}) as _));
			}
		}

		if capabilities.contains(offchain::Capabilities::STATEMENT_STORE) {
			if let Some(store) = self.statement_store.read().as_ref().and_then(|x| x.upgrade()) {
				extensions.register(sp_statement_store::runtime_api::StatementStoreExt(store));
			}
		}
		if capabilities.contains(offchain::Capabilities::OFFCHAIN_DB_READ) ||
			capabilities.contains(offchain::Capabilities::OFFCHAIN_DB_WRITE)
		{
			if let Some(offchain_db) = self.offchain_db.as_ref() {
				extensions.register(OffchainDbExt::new(offchain::LimitedExternalities::new(
					capabilities,
					offchain_db.create(),
				)));
			}
		}

		if let ExecutionContext::OffchainCall(Some(ext)) = context {
			extensions.register(OffchainWorkerExt::new(offchain::LimitedExternalities::new(
				capabilities,
				ext.0,
			)));
		}

		extensions.register(ReadRuntimeVersionExt::new(self.read_runtime_version.clone()));

		extensions
	}

	/// Create `ExecutionManager` and `Extensions` for given offchain call.
	///
	/// Based on the execution context and capabilities it produces
	/// the right manager and extensions object to support desired set of APIs.
	pub fn manager_and_extensions<E: std::fmt::Debug>(
		&self,
		block_hash: Block::Hash,
		block_number: NumberFor<Block>,
		context: ExecutionContext,
	) -> (ExecutionManager<DefaultHandler<E>>, Extensions) {
		let manager = match context {
			ExecutionContext::BlockConstruction => self.strategies.block_construction.get_manager(),
			ExecutionContext::Syncing => self.strategies.syncing.get_manager(),
			ExecutionContext::Importing => self.strategies.importing.get_manager(),
			ExecutionContext::OffchainCall(Some((_, capabilities))) if capabilities.is_all() =>
				self.strategies.offchain_worker.get_manager(),
			ExecutionContext::OffchainCall(_) => self.strategies.other.get_manager(),
		};

		(manager, self.extensions(block_hash, block_number, context))
	}
}

/// A wrapper type to pass `BlockId` to the actual transaction pool.
struct TransactionPoolAdapter<Block: BlockT> {
	at: BlockId<Block>,
	pool: Arc<dyn OffchainSubmitTransaction<Block>>,
}

impl<Block: BlockT> offchain::TransactionPool for TransactionPoolAdapter<Block> {
	fn submit_transaction(&mut self, data: Vec<u8>) -> Result<(), ()> {
		let xt = match Block::Extrinsic::decode(&mut &*data) {
			Ok(xt) => xt,
			Err(e) => {
				log::warn!("Unable to decode extrinsic: {:?}: {}", data, e);
				return Err(())
			},
		};

		self.pool.submit_at(&self.at, xt)
	}
}
