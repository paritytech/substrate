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

//! Configuration of the transaction protocol

use futures::prelude::*;
use sc_network_common::ExHashT;
use sp_runtime::traits::Block as BlockT;
use std::{collections::HashMap, future::Future, pin::Pin, time};

/// Interval at which we propagate transactions;
pub(crate) const PROPAGATE_TIMEOUT: time::Duration = time::Duration::from_millis(2900);

/// Maximum number of known transaction hashes to keep for a peer.
///
/// This should be approx. 2 blocks full of transactions for the network to function properly.
pub(crate) const MAX_KNOWN_TRANSACTIONS: usize = 10240; // ~300kb per peer + overhead.

/// Maximum allowed size for a transactions notification.
pub(crate) const MAX_TRANSACTIONS_SIZE: u64 = 16 * 1024 * 1024;

/// Maximum number of transaction validation request we keep at any moment.
pub(crate) const MAX_PENDING_TRANSACTIONS: usize = 8192;

/// Result of the transaction import.
#[derive(Clone, Copy, Debug)]
pub enum TransactionImport {
	/// Transaction is good but already known by the transaction pool.
	KnownGood,
	/// Transaction is good and not yet known.
	NewGood,
	/// Transaction is invalid.
	Bad,
	/// Transaction import was not performed.
	None,
}

/// Future resolving to transaction import result.
pub type TransactionImportFuture = Pin<Box<dyn Future<Output = TransactionImport> + Send>>;

/// Transaction pool interface
pub trait TransactionPool<H: ExHashT, B: BlockT>: Send + Sync {
	/// Get transactions from the pool that are ready to be propagated.
	fn transactions(&self) -> Vec<(H, B::Extrinsic)>;
	/// Get hash of transaction.
	fn hash_of(&self, transaction: &B::Extrinsic) -> H;
	/// Import a transaction into the pool.
	///
	/// This will return future.
	fn import(&self, transaction: B::Extrinsic) -> TransactionImportFuture;
	/// Notify the pool about transactions broadcast.
	fn on_broadcasted(&self, propagations: HashMap<H, Vec<String>>);
	/// Get transaction by hash.
	fn transaction(&self, hash: &H) -> Option<B::Extrinsic>;
}

/// Dummy implementation of the [`TransactionPool`] trait for a transaction pool that is always
/// empty and discards all incoming transactions.
///
/// Requires the "hash" type to implement the `Default` trait.
///
/// Useful for testing purposes.
pub struct EmptyTransactionPool;

impl<H: ExHashT + Default, B: BlockT> TransactionPool<H, B> for EmptyTransactionPool {
	fn transactions(&self) -> Vec<(H, B::Extrinsic)> {
		Vec::new()
	}

	fn hash_of(&self, _transaction: &B::Extrinsic) -> H {
		Default::default()
	}

	fn import(&self, _transaction: B::Extrinsic) -> TransactionImportFuture {
		Box::pin(future::ready(TransactionImport::KnownGood))
	}

	fn on_broadcasted(&self, _: HashMap<H, Vec<String>>) {}

	fn transaction(&self, _h: &H) -> Option<B::Extrinsic> {
		None
	}
}
