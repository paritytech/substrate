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

//! Implementation of the `chainHead_storage` method.

use std::{marker::PhantomData, sync::Arc};

use jsonrpsee::SubscriptionSink;
use sc_client_api::{Backend, ChildInfo, StorageKey, StorageProvider};
use sp_api::BlockT;
use sp_core::storage::well_known_keys;

use super::{
	event::{
		ChainHeadStorageEvent, ItemsEvent, StorageQuery, StorageQueryType, StorageResult,
		StorageResultType,
	},
	hex_string, ErrorEvent,
};

/// The maximum number of items the `chainHead_storage` can return
/// before paginations is required.
const MAX_ITER_ITEMS: usize = 10;

/// The query type of an interation.
enum IterQueryType {
	/// Iterating over (key, value) pairs.
	Value,
	/// Iterating over (key, hash) pairs.
	Hash,
}

/// Generates the events of the `chainHead_storage` method.
pub struct ChainHeadStorage<Client, Block, BE> {
	/// Substrate client.
	client: Arc<Client>,
	_phantom: PhantomData<(Block, BE)>,
}

impl<Client, Block, BE> ChainHeadStorage<Client, Block, BE> {
	/// Constructs a new [`ChainHeadStorage`].
	pub fn new(client: Arc<Client>) -> Self {
		Self { client, _phantom: PhantomData }
	}
}

/// Checks if the provided key (main or child key) is valid
/// for queries.
///
/// Keys that are identical to `:child_storage:` or `:child_storage:default:`
/// are not queryable.
fn is_key_queryable(key: &[u8]) -> bool {
	!well_known_keys::is_default_child_storage_key(key) &&
		!well_known_keys::is_child_storage_key(key)
}

/// The result of making a query call.
type QueryResult = Result<Option<StorageResult>, ChainHeadStorageEvent>;

/// The result of iterating over keys.
type QueryIterResult = Result<Vec<StorageResult>, ChainHeadStorageEvent>;

impl<Client, Block, BE> ChainHeadStorage<Client, Block, BE>
where
	Block: BlockT + 'static,
	BE: Backend<Block> + 'static,
	Client: StorageProvider<Block, BE> + 'static,
{
	/// Fetch the value from storage.
	fn query_storage_value(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
		child_key: Option<&ChildInfo>,
	) -> QueryResult {
		let result = if let Some(child_key) = child_key {
			self.client.child_storage(hash, child_key, key)
		} else {
			self.client.storage(hash, key)
		};

		result
			.map(|opt| {
				QueryResult::Ok(opt.map(|storage_data| StorageResult {
					key: hex_string(&key.0),
					result: StorageResultType::Value(hex_string(&storage_data.0)),
				}))
			})
			.unwrap_or_else(|err| {
				QueryResult::Err(ChainHeadStorageEvent::Error(ErrorEvent {
					error: err.to_string(),
				}))
			})
	}

	/// Fetch the hash of a value from storage.
	fn query_storage_hash(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
		child_key: Option<&ChildInfo>,
	) -> QueryResult {
		let result = if let Some(child_key) = child_key {
			self.client.child_storage_hash(hash, child_key, key)
		} else {
			self.client.storage_hash(hash, key)
		};

		result
			.map(|opt| {
				QueryResult::Ok(opt.map(|storage_data| StorageResult {
					key: hex_string(&key.0),
					result: StorageResultType::Hash(hex_string(&storage_data.as_ref())),
				}))
			})
			.unwrap_or_else(|err| {
				QueryResult::Err(ChainHeadStorageEvent::Error(ErrorEvent {
					error: err.to_string(),
				}))
			})
	}

	/// Handle iterating over (key, value) or (key, hash) pairs.
	fn query_storage_iter(
		&self,
		hash: Block::Hash,
		key: &StorageKey,
		child_key: Option<&ChildInfo>,
		ty: IterQueryType,
	) -> QueryIterResult {
		let keys_iter = if let Some(child_key) = child_key {
			self.client.child_storage_keys(hash, child_key.to_owned(), Some(key), None)
		} else {
			self.client.storage_keys(hash, Some(key), None)
		}
		.map_err(|err| ChainHeadStorageEvent::Error(ErrorEvent { error: err.to_string() }))?;

		let mut ret = Vec::with_capacity(MAX_ITER_ITEMS);
		let mut keys_iter = keys_iter.take(MAX_ITER_ITEMS);
		while let Some(key) = keys_iter.next() {
			let result = match ty {
				IterQueryType::Value => self.query_storage_value(hash, &key, child_key),
				IterQueryType::Hash => self.query_storage_hash(hash, &key, child_key),
			}?;

			if let Some(result) = result {
				ret.push(result);
			}
		}

		QueryIterResult::Ok(ret)
	}

	/// Generate the block events for the `chainHead_storage` method.
	pub fn generate_events(
		&self,
		mut sink: SubscriptionSink,
		hash: Block::Hash,
		items: Vec<StorageQuery<StorageKey>>,
		child_key: Option<ChildInfo>,
	) {
		if let Some(child_key) = child_key.as_ref() {
			if !is_key_queryable(child_key.storage_key()) {
				let _ = sink.send(&ChainHeadStorageEvent::Done);
				return
			}
		}

		let mut storage_results = Vec::with_capacity(items.len());
		for item in items {
			if !is_key_queryable(&item.key.0) {
				continue
			}

			match item.query_type {
				StorageQueryType::Value => {
					match self.query_storage_value(hash, &item.key, child_key.as_ref()) {
						Ok(Some(value)) => storage_results.push(value),
						Ok(None) => continue,
						Err(err) => {
							let _ = sink.send(&err);
							return
						},
					}
				},
				StorageQueryType::Hash =>
					match self.query_storage_hash(hash, &item.key, child_key.as_ref()) {
						Ok(Some(value)) => storage_results.push(value),
						Ok(None) => continue,
						Err(err) => {
							let _ = sink.send(&err);
							return
						},
					},
				StorageQueryType::DescendantsValues => match self.query_storage_iter(
					hash,
					&item.key,
					child_key.as_ref(),
					IterQueryType::Value,
				) {
					Ok(values) => storage_results.extend(values),
					Err(err) => {
						let _ = sink.send(&err);
						return
					},
				},
				StorageQueryType::DescendantsHashes => match self.query_storage_iter(
					hash,
					&item.key,
					child_key.as_ref(),
					IterQueryType::Hash,
				) {
					Ok(values) => storage_results.extend(values),
					Err(err) => {
						let _ = sink.send(&err);
						return
					},
				},
				_ => continue,
			};
		}

		if !storage_results.is_empty() {
			let event = ChainHeadStorageEvent::Items(ItemsEvent { items: storage_results });
			let _ = sink.send(&event);
		}

		let _ = sink.send(&ChainHeadStorageEvent::Done);
	}
}
