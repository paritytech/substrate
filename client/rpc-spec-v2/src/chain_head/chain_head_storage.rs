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

use std::{collections::VecDeque, marker::PhantomData, sync::Arc};

use sc_client_api::{Backend, ChildInfo, StorageKey, StorageProvider};
use sc_utils::mpsc::TracingUnboundedSender;
use sp_api::BlockT;
use sp_core::storage::well_known_keys;

use crate::chain_head::event::OperationStorageItems;

use super::{
	event::{
		OperationError, OperationId, StorageQuery, StorageQueryType, StorageResult,
		StorageResultType,
	},
	hex_string,
	subscription::BlockGuard,
	FollowEvent,
};

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
	/// Queue of operations that may require pagination.
	iter_operations: VecDeque<QueryIter>,
	/// The maximum number of items reported by the `chainHead_storage` before
	/// pagination is required.
	operation_max_storage_items: usize,
	_phandom: PhantomData<(BE, Block)>,
}

impl<Client, Block, BE> ChainHeadStorage<Client, Block, BE> {
	/// Constructs a new [`ChainHeadStorage`].
	pub fn new(client: Arc<Client>, operation_max_storage_items: usize) -> Self {
		Self {
			client,
			iter_operations: VecDeque::new(),
			operation_max_storage_items,
			_phandom: PhantomData,
		}
	}
}

/// Query to iterate over storage.
struct QueryIter {
	/// The next key from which the iteration should continue.
	next_key: StorageKey,
	/// The type of the query (either value or hash).
	ty: IterQueryType,
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
type QueryResult = Result<Option<StorageResult>, String>;

/// The result of iterating over keys.
type QueryIterResult = Result<(Vec<StorageResult>, Option<QueryIter>), String>;

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
			.unwrap_or_else(|error| QueryResult::Err(error.to_string()))
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
			.unwrap_or_else(|error| QueryResult::Err(error.to_string()))
	}

	/// Iterate over at most `operation_max_storage_items` keys.
	///
	/// Returns the storage result with a potential next key to resume iteration.
	fn query_storage_iter_pagination(
		&self,
		query: QueryIter,
		hash: Block::Hash,
		child_key: Option<&ChildInfo>,
	) -> QueryIterResult {
		let QueryIter { next_key, ty } = query;

		let mut keys_iter = if let Some(child_key) = child_key {
			self.client
				.child_storage_keys(hash, child_key.to_owned(), Some(&next_key), None)
		} else {
			self.client.storage_keys(hash, Some(&next_key), None)
		}
		.map_err(|err| err.to_string())?;

		let mut ret = Vec::with_capacity(self.operation_max_storage_items);
		for _ in 0..self.operation_max_storage_items {
			let Some(key) = keys_iter.next() else { break };

			let result = match ty {
				IterQueryType::Value => self.query_storage_value(hash, &key, child_key),
				IterQueryType::Hash => self.query_storage_hash(hash, &key, child_key),
			}?;

			if let Some(value) = result {
				ret.push(value);
			}
		}

		// Save the next key if any to continue the iteration.
		let maybe_next_query = keys_iter.next().map(|next_key| QueryIter { next_key, ty });
		Ok((ret, maybe_next_query))
	}

	/// Iterate over (key, hash) and (key, value) generating the `WaitingForContinue` event if
	/// necessary.
	async fn generate_storage_iter_events(
		&mut self,
		mut block_guard: BlockGuard<Block, BE>,
		hash: Block::Hash,
		child_key: Option<ChildInfo>,
	) {
		let sender = block_guard.response_sender();
		let operation = block_guard.operation();

		while let Some(query) = self.iter_operations.pop_front() {
			if operation.was_stopped() {
				return
			}

			let result = self.query_storage_iter_pagination(query, hash, child_key.as_ref());
			let (events, maybe_next_query) = match result {
				QueryIterResult::Ok(result) => result,
				QueryIterResult::Err(error) => {
					send_error::<Block>(&sender, operation.operation_id(), error.to_string());
					return
				},
			};

			if !events.is_empty() {
				// Send back the results of the iteration produced so far.
				let _ = sender.unbounded_send(FollowEvent::<Block::Hash>::OperationStorageItems(
					OperationStorageItems { operation_id: operation.operation_id(), items: events },
				));
			}

			if let Some(next_query) = maybe_next_query {
				let _ =
					sender.unbounded_send(FollowEvent::<Block::Hash>::OperationWaitingForContinue(
						OperationId { operation_id: operation.operation_id() },
					));

				// The operation might be continued or cancelled only after the
				// `OperationWaitingForContinue` is generated above.
				operation.wait_for_continue().await;

				// Give a chance for the other items to advance next time.
				self.iter_operations.push_back(next_query);
			}
		}

		if operation.was_stopped() {
			return
		}

		let _ =
			sender.unbounded_send(FollowEvent::<Block::Hash>::OperationStorageDone(OperationId {
				operation_id: operation.operation_id(),
			}));
	}

	/// Generate the block events for the `chainHead_storage` method.
	pub async fn generate_events(
		&mut self,
		mut block_guard: BlockGuard<Block, BE>,
		hash: Block::Hash,
		items: Vec<StorageQuery<StorageKey>>,
		child_key: Option<ChildInfo>,
	) {
		let sender = block_guard.response_sender();
		let operation = block_guard.operation();

		if let Some(child_key) = child_key.as_ref() {
			if !is_key_queryable(child_key.storage_key()) {
				let _ = sender.unbounded_send(FollowEvent::<Block::Hash>::OperationStorageDone(
					OperationId { operation_id: operation.operation_id() },
				));
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
						Err(error) => {
							send_error::<Block>(&sender, operation.operation_id(), error);
							return
						},
					}
				},
				StorageQueryType::Hash =>
					match self.query_storage_hash(hash, &item.key, child_key.as_ref()) {
						Ok(Some(value)) => storage_results.push(value),
						Ok(None) => continue,
						Err(error) => {
							send_error::<Block>(&sender, operation.operation_id(), error);
							return
						},
					},
				StorageQueryType::DescendantsValues => self
					.iter_operations
					.push_back(QueryIter { next_key: item.key, ty: IterQueryType::Value }),
				StorageQueryType::DescendantsHashes => self
					.iter_operations
					.push_back(QueryIter { next_key: item.key, ty: IterQueryType::Hash }),
				_ => continue,
			};
		}

		if !storage_results.is_empty() {
			let _ = sender.unbounded_send(FollowEvent::<Block::Hash>::OperationStorageItems(
				OperationStorageItems {
					operation_id: operation.operation_id(),
					items: storage_results,
				},
			));
		}

		self.generate_storage_iter_events(block_guard, hash, child_key).await
	}
}

/// Build and send the opaque error back to the `chainHead_follow` method.
fn send_error<Block: BlockT>(
	sender: &TracingUnboundedSender<FollowEvent<Block::Hash>>,
	operation_id: String,
	error: String,
) {
	let _ = sender.unbounded_send(FollowEvent::<Block::Hash>::OperationError(OperationError {
		operation_id,
		error,
	}));
}
