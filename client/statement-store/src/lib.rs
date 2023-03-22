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

//! Disk-backed statement store.

#![warn(missing_docs)]
#![warn(unused_extern_crates)]

mod metrics;

pub use sp_statement_store::{StatementStore, Error};

use std::{collections::{HashSet, HashMap, BinaryHeap}, sync::Arc};
use parking_lot::RwLock;
use metrics::MetricsLink as PrometheusMetrics;
use prometheus_endpoint::Registry as PrometheusRegistry;
use sp_statement_store::{Statement, Topic, DecryptionKey, Result, Hash, BlockHash, SubmitResult, NetworkPriority};
use sp_statement_store::runtime_api::{ValidateStatement, ValidStatement, InvalidStatement, StatementSource};
use sp_core::{Encode, Decode};
use sp_api::ProvideRuntimeApi;
use sp_runtime::traits::Block as BlockT;


const KEY_VERSION: &[u8] = b"version".as_slice();
const CURRENT_VERSION: u32 = 1;

const LOG_TARGET: &str = "statement";

const EXPIRE_AFTER: u64 = 24 * 60 * 60; //24h
const PURGE_AFTER: u64 = 2 * 24 * 60 * 60; //48h

/// Suggested maintenance period. A good value to call `Store::maintain` with.
#[allow(dead_code)]
pub const MAINTENANCE_PERIOD: std::time::Duration = std::time::Duration::from_secs(30);

mod col {
	pub const META: u8 = 0;
	pub const STATEMENTS: u8 = 1;

	pub const COUNT: u8 = 2;
}

#[derive(PartialEq, Eq)]
struct EvictionPriority {
	hash: Hash,
	priority: u64,
	timestamp: u64,
}

impl PartialOrd for EvictionPriority {
	fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
		Some(self.priority.cmp(&other.priority).then_with(|| self.timestamp.cmp(&other.timestamp)).reverse())
	}
}

impl Ord for EvictionPriority {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		self.priority.cmp(&other.priority).then_with(|| self.timestamp.cmp(&other.timestamp)).reverse()
	}
}

#[derive(Default)]
struct Index {
	by_topic: HashMap<Topic, HashSet<Hash>>,
	by_dec_key: HashMap<DecryptionKey, HashSet<Hash>>,
	all_topics: HashMap<Hash, ([Option<Topic>; 4], Option<DecryptionKey>)>,
	by_priority: BinaryHeap<EvictionPriority>,
	entries: HashMap<Hash, StatementMeta>,
	expired: HashMap<Hash, StatementMeta>,
	max_entries: usize,
}

struct ClientWrapper<Block, Client>  {
	client: Arc<Client>,
	_block: std::marker::PhantomData<Block>,
}

impl<Block, Client> ClientWrapper<Block, Client>
	where
		Block: BlockT,
		Block::Hash: From<BlockHash>,
		Client: ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
		Client::Api: ValidateStatement<Block>,
{
	fn validate_statement(
		&self,
		block: BlockHash,
		source: StatementSource,
		statement: Statement,
	) -> std::result::Result<ValidStatement, InvalidStatement> {
		let api = self.client.runtime_api();
		let block = block.into();
		match api.validate_statement(block, source, statement) {
			Ok(r) => r,
			Err(_) => {
				Err(InvalidStatement::InternalError)
			}
		}
	}
}

/// Statement store.
pub struct Store {
	db: parity_db::Db,
	index: RwLock<Index>,
	validate_fn: Box<dyn Fn(BlockHash, StatementSource, Statement) -> std::result::Result<ValidStatement, InvalidStatement> + Send + Sync>,
	time_overrite: Option<u64>,
	metrics: PrometheusMetrics,
}

#[derive(Encode, Decode, Clone)]
struct StatementMeta {
	priority: u64,
	timestamp: u64,
}

#[derive(Encode, Decode)]
struct StatementWithMeta {
	meta: StatementMeta,
	statement: Statement,
}

enum IndexQuery {
	Unknown,
	Exists(u64),
	Expired(u64),
}

impl Index {
	fn insert_with_meta(&mut self, hash: Hash, statement: StatementWithMeta) {
		let mut all_topics = [None; 4];
		let mut nt = 0;
		let StatementWithMeta { statement, meta } = statement;
		while let Some(t) = statement.topic(nt) {
			self.by_topic.entry(t).or_default().insert(hash);
			all_topics[nt] = Some(t);
			nt += 1;
		}
		let key = statement.decryption_key();
		if let Some(k) = &key {
			self.by_dec_key.entry(k.clone()).or_default().insert(hash);
		}
		if nt > 0 || key.is_some() {
			self.all_topics.insert(hash, (all_topics, key));
		}
		self.expired.remove(&hash);
		if self.entries.insert(hash, meta.clone()).is_none() {
			self.by_priority.push(EvictionPriority {
				hash,
				priority: meta.priority,
				timestamp: meta.timestamp,
			});
		}
	}

	fn query(&self, hash: &Hash) -> IndexQuery {
		if let Some(meta) = self.entries.get(hash) {
			return IndexQuery::Exists(meta.priority);
		}
		if let Some(meta) = self.expired.get(hash) {
			return IndexQuery::Expired(meta.priority);
		}
		IndexQuery::Unknown
	}

	fn insert_expired(&mut self, hash: Hash, meta: StatementMeta) {
		self.expired.insert(hash, meta);
	}

	fn is_expired(&self, hash: &Hash) -> bool {
		self.expired.contains_key(hash)
	}

	fn iter(&self, key: Option<DecryptionKey>, topics: &[Topic], mut f: impl FnMut(&Hash) -> Result<()>) -> Result<()> {
		let mut sets: [Option<&HashSet<Hash>>; 4] = Default::default();
		let mut num_sets = 0;
		for t in topics {
			sets[num_sets] = self.by_topic.get(t);
			if sets[num_sets].is_some() {
				num_sets += 1;
			}
		}
		if num_sets == 0 && key.is_none() {
			// Iterate all entries
			for h in self.entries.keys() {
				f(h)?
			}
		} else {
			// Start with the smallest topic set or the key set.
			sets[0..num_sets].sort_by_key(|s| s.map_or(0, HashSet::len));
			if let Some(key) = key {
				let key_set = if let Some(set) = self.by_dec_key.get(&key) { set } else { return Ok(()) };
				for item in key_set {
					if sets.iter().all(|set| set.unwrap().contains(item)) {
						f(item)?
					}
				}
			} else {
				for item in sets[0].unwrap() {
					if sets[1 .. num_sets].iter().all(|set| set.unwrap().contains(item)) {
						f(item)?
					}
				}
			}
		}
		Ok(())
	}

	fn maintain(&mut self, current_time: u64) -> Vec<(parity_db::ColId, Vec<u8>, Option<Vec<u8>>)> {
		// Purge previously expired messages.
		let mut purged = Vec::new();
		self.expired.retain(|hash, meta| {
			if meta.timestamp + PURGE_AFTER > current_time {
				purged.push((col::STATEMENTS, hash.to_vec(), None));
				false
			} else {
				true
			}
		});

		// Expire messages.
		let mut num_expired = 0;
		self.entries.retain(|hash, meta| {
			if meta.timestamp + EXPIRE_AFTER > current_time {
				if let Some((topics, key)) = self.all_topics.remove(hash) {
					for t in topics {
						if let Some(t) = t {
							if let Some(set) = self.by_topic.get_mut(&t) {
								set.remove(hash);
							}
						}
					}
					if let Some(k) = key {
						if let Some(set) = self.by_dec_key.get_mut(&k) {
							set.remove(hash);
						}
					}
				}
				self.expired.insert(hash.clone(), meta.clone());
				num_expired += 1;
				false
			} else {
				true
			}
		});
		if num_expired > 0 {
			// Rebuild the priority queue
			self.by_priority = self.entries.iter().map(|(hash, meta)| EvictionPriority {
				hash: hash.clone(),
				priority: meta.priority,
				timestamp: meta.timestamp,
			}).collect();
		}
		purged
	}

	fn evict(&mut self) -> Vec<(parity_db::ColId, Vec<u8>, Option<Vec<u8>>)> {
		let mut evicted_set = Vec::new();
		while self.by_priority.len() > self.max_entries {
			if let Some(evicted) = self.by_priority.pop() {
				self.entries.remove(&evicted.hash);
				if let Some((topics, key)) = self.all_topics.remove(&evicted.hash) {
					for t in topics {
						if let Some(t) = t {
							if let Some(set) = self.by_topic.get_mut(&t) {
								set.remove(&evicted.hash);
							}
						}
					}
					if let Some(k) = key {
						if let Some(set) = self.by_dec_key.get_mut(&k) {
							set.remove(&evicted.hash);
						}
					}
				}
				evicted_set.push((col::STATEMENTS, evicted.hash.to_vec(), None));
			} else {
				break;
			}
		}
		evicted_set
	}
}

impl Store {
	/// Create a new shared store instance. There should only be one per process.
	pub fn new<Block, Client>(
		path: &std::path::Path,
		client: Arc<Client>,
		prometheus: Option<&PrometheusRegistry>,
	) -> Result<Arc<Store>>
	where
		Block: BlockT,
		Block::Hash: From<BlockHash>,
		Client: ProvideRuntimeApi<Block>
		+ Send
		+ Sync
		+ 'static,
		Client::Api: ValidateStatement<Block>,
	{
		let mut path: std::path::PathBuf = path.into();
		path.pop();
		path.push("statement");

		let mut config = parity_db::Options::with_columns(&path, col::COUNT);

		let mut statement_col = &mut config.columns[col::STATEMENTS as usize];
		statement_col.ref_counted = false;
		statement_col.preimage = true;
		statement_col.uniform = true;
		let db = parity_db::Db::open_or_create(&config).map_err(|e| Error::Db(e.to_string()))?;
		match db.get(col::META, &KEY_VERSION).map_err(|e| Error::Db(e.to_string()))? {
			Some(version) => {
				let version = u32::from_le_bytes(version.try_into()
					.map_err(|_| Error::Db("Error reading database version".into()))?);
				if version != CURRENT_VERSION {
					return Err(Error::Db(format!("Unsupported database version: {version}")));
				}
			},
			None => {
				db.commit(
					[(col::META, KEY_VERSION.to_vec(),  Some(CURRENT_VERSION.to_le_bytes().to_vec()))]
				).map_err(|e| Error::Db(e.to_string()))?;
			}
		}

		let index = Index::default();
		let validator = ClientWrapper { client, _block: Default::default() };
		let validate_fn = Box::new(move |block, source, statement| validator.validate_statement(block, source, statement));

		let store = Arc::new(Store {
			db,
			index: RwLock::new(index),
			validate_fn,
			time_overrite: None,
			metrics: PrometheusMetrics::new(prometheus),
		});
		store.populate()?;
		Ok(store)
	}

	fn populate(&self) -> Result<()> {
		let current_time = self.timestamp();
		let mut index = self.index.write();
		self.db.iter_column_while(col::STATEMENTS, |item| {
			let statement = item.value;
			if let Ok(statement_with_meta) = StatementWithMeta::decode(&mut statement.as_slice()) {
				let hash = statement_with_meta.statement.hash();
				if statement_with_meta.meta.timestamp + EXPIRE_AFTER > current_time {
					index.insert_expired(hash, statement_with_meta.meta);
				} else {
					index.insert_with_meta(hash, statement_with_meta);
				}
			}
			true
		}).map_err(|e| Error::Db(e.to_string()))?;

		Ok(())
	}

	fn collect_statements<R>(&self, key: Option<DecryptionKey>, match_all_topics: &[Topic], mut f: impl FnMut(Statement) -> Option<R> ) -> Result<Vec<R>> {
		let mut result = Vec::new();
		let index = self.index.read();
		index.iter(key, match_all_topics, |hash| {
			match self.db.get(col::STATEMENTS, hash).map_err(|e| Error::Db(e.to_string()))? {
				Some(entry) => {
					if let Ok(statement) = StatementWithMeta::decode(&mut entry.as_slice()) {
						if let Some(data) = f(statement.statement) {
							result.push(data);
						}
					} else {
						// DB inconsistency
						log::warn!(target: LOG_TARGET, "Corrupt statement {:?}", hash);
					}

				}
				None => {
					// DB inconsistency
					log::warn!(target: LOG_TARGET, "Missing statement {:?}", hash);
				}
			}
			Ok(())
		})?;
		Ok(result)
	}

	/// Perform periodic store maintenance
	pub fn maintain(&self) {
		let deleted = self.index.write().maintain(self.timestamp());
		let count = deleted.len() as u64;
		if let Err(e) = self.db.commit(deleted) {
			log::warn!(target: LOG_TARGET, "Error writing to the statement database: {:?}", e);
		} else {
			self.metrics.report(|metrics| metrics.statements_pruned.inc_by(count));
		}
	}

	fn timestamp(&self) -> u64 {
		self.time_overrite.unwrap_or_else(||
			std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default().as_secs())
	}
}

impl StatementStore for Store {
	fn dump_encoded(&self) -> Result<Vec<(Hash, Vec<u8>)>> {
		let mut result = Vec::new();
		self.db.iter_column_while(col::STATEMENTS, |item| {
			if let Ok(entry) = StatementWithMeta::decode(&mut item.value.as_slice()) {
				entry.statement.using_encoded(|statement| {
					let hash = sp_statement_store::hash_encoded(statement);
					if !self.index.read().is_expired(&hash) {
						result.push((hash, entry.statement.encode()));
					}
				});
			}
			true
		}).map_err(|e| Error::Db(e.to_string()))?;
		Ok(result)
	}

	/// Return all statements.
	fn dump(&self) -> Result<Vec<(Hash, Statement)>> {
		let mut result = Vec::new();
		self.db.iter_column_while(col::STATEMENTS, |item| {
			if let Ok(entry) = StatementWithMeta::decode(&mut item.value.as_slice()) {
				let hash = entry.statement.hash();
				if !self.index.read().is_expired(&hash) {
					result.push((hash, entry.statement));
				}
			}
			true
		}).map_err(|e| Error::Db(e.to_string()))?;
		Ok(result)
	}

	/// Returns a statement by hash.
	fn statement(&self, hash: &Hash) -> Result<Option<Statement>> {
		Ok(match self.db.get(col::STATEMENTS, hash.as_slice()).map_err(|e| Error::Db(e.to_string()))? {
			Some(entry) => {
				Some(StatementWithMeta::decode(&mut entry.as_slice()).map_err(|e| Error::Decode(e.to_string()))?.statement)
			}
			None => None,
		})
	}

	/// Return the data of all known statements which include all topics and have no `DecryptionKey` field.
	fn broadcasts(&self, match_all_topics: &[Topic]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(None, match_all_topics, |statement| statement.into_data())
	}

	/// Return the data of all known statements whose decryption key is identified as `dest` (this will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the private key for symmetric ciphers).
	fn posted(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(Some(dest), match_all_topics, |statement| statement.into_data())
	}

	/// Return the decrypted data of all known statements whose decryption key is identified as `dest`. The key must be available to the client.
	fn posted_clear(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(Some(dest), match_all_topics, |statement| statement.into_data())
	}

	/// Submit a statement to the store. Validates the statement and returns validation result.
	fn submit(&self, statement: Statement, source: StatementSource) -> SubmitResult {
		let hash = statement.hash();
		let priority = match self.index.read().query(&hash) {
			IndexQuery::Expired(priority) => {
				if !source.can_be_resubmitted() {
					return SubmitResult::KnownExpired;
				}
				priority
			}
			IndexQuery::Exists(priority) => {
				if !source.can_be_resubmitted() {
					return SubmitResult::Known;
				}
				priority
			}
			IndexQuery::Unknown => {
				// Validate.
				let validation_result = (self.validate_fn)(Default::default(), source, statement.clone());
				match validation_result {
					Ok(ValidStatement { priority }) => priority,
					Err(InvalidStatement::BadProof) => {
						log::debug!(target: LOG_TARGET, "Statement validation failed: BadProof, {:?}", statement);
						self.metrics.report(|metrics| metrics.validations_invalid.inc());
						return SubmitResult::Bad("Bad statement proof")
					},
					Err(InvalidStatement::NoProof) =>{
						log::debug!(target: LOG_TARGET, "Statement validation failed: NoProof, {:?}", statement);
						self.metrics.report(|metrics| metrics.validations_invalid.inc());
						return SubmitResult::Bad("Missing statement proof")
					},
					Err(InvalidStatement::InternalError) => {
						return SubmitResult::InternalError(Error::Runtime)
					},
				}
			}
		};

		// Commit to the db prior to locking the index.
		let statement_with_meta = StatementWithMeta {
			meta: StatementMeta {
				priority,
				timestamp: self.timestamp(),
			},
			statement,
		};

		let mut commit = self.index.write().evict();
		commit.push((col::STATEMENTS, hash.to_vec(), Some(statement_with_meta.encode())));
		if let Err(e) = self.db.commit(commit) {
			log::debug!(target: LOG_TARGET, "Statement validation failed: database error {}, {:?}", e, statement_with_meta.statement);
			return SubmitResult::InternalError(Error::Db(e.to_string()));
		}
		self.metrics.report(|metrics| metrics.submitted_statements.inc());
		let mut index = self.index.write();
		index.insert_with_meta(hash, statement_with_meta);
		let network_priority = if priority > 0 { NetworkPriority::High } else { NetworkPriority::Low };
		SubmitResult::New(network_priority)
	}

	/// Submit a SCALE-encoded statement.
	fn submit_encoded(&self, mut statement: &[u8], source: StatementSource) -> SubmitResult {
		match Statement::decode(&mut statement) {
			Ok(decoded) => self.submit(decoded, source),
			Err(e) => {
				log::debug!(target: LOG_TARGET, "Error decoding submitted statement. Failed with: {}", e);
				SubmitResult::Bad("Bad SCALE encoding")
			}
		}
	}
}

#[cfg(test)]
mod tests {
}



