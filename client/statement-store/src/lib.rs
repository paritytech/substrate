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

pub use sp_statement_store::{Error, StatementStore};

use metrics::MetricsLink as PrometheusMetrics;
use parking_lot::RwLock;
use prometheus_endpoint::Registry as PrometheusRegistry;
use sp_api::ProvideRuntimeApi;
use sp_blockchain::HeaderBackend;
use sp_core::{hexdisplay::HexDisplay, Decode, Encode};
use sp_runtime::traits::Block as BlockT;
use sp_statement_store::{
	runtime_api::{InvalidStatement, StatementSource, ValidStatement, ValidateStatement},
	BlockHash, DecryptionKey, Hash, NetworkPriority, Proof, Result, Statement, SubmitResult, Topic,
};
use std::{
	collections::{BinaryHeap, HashMap, HashSet},
	sync::Arc,
};

const KEY_VERSION: &[u8] = b"version".as_slice();
const CURRENT_VERSION: u32 = 1;

const LOG_TARGET: &str = "statement-store";

const EXPIRE_AFTER: u64 = 24 * 60 * 60; //24h
const PURGE_AFTER: u64 = 2 * 24 * 60 * 60; //48h
const MAX_LIVE_STATEMENTS: usize = 8192;

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
		Some(
			self.priority
				.cmp(&other.priority)
				.then_with(|| self.timestamp.cmp(&other.timestamp))
				.reverse(),
		)
	}
}

impl Ord for EvictionPriority {
	fn cmp(&self, other: &Self) -> std::cmp::Ordering {
		self.priority
			.cmp(&other.priority)
			.then_with(|| self.timestamp.cmp(&other.timestamp))
			.reverse()
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

struct ClientWrapper<Block, Client> {
	client: Arc<Client>,
	_block: std::marker::PhantomData<Block>,
}

impl<Block, Client> ClientWrapper<Block, Client>
where
	Block: BlockT,
	Block::Hash: From<BlockHash>,
	Client: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
	Client::Api: ValidateStatement<Block>,
{
	fn validate_statement(
		&self,
		block: Option<BlockHash>,
		source: StatementSource,
		statement: Statement,
	) -> std::result::Result<ValidStatement, InvalidStatement> {
		let api = self.client.runtime_api();
		let block = block.map(Into::into).unwrap_or_else(|| {
			// Validate against the finalized state.
			self.client.info().finalized_hash
		});
		match api.validate_statement(block, source, statement) {
			Ok(r) => r,
			Err(_) => Err(InvalidStatement::InternalError),
		}
	}
}

/// Statement store.
pub struct Store {
	db: parity_db::Db,
	index: RwLock<Index>,
	validate_fn: Box<
		dyn Fn(
				Option<BlockHash>,
				StatementSource,
				Statement,
			) -> std::result::Result<ValidStatement, InvalidStatement>
			+ Send
			+ Sync,
	>,
	time_override: Option<u64>,
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
			return IndexQuery::Exists(meta.priority)
		}
		if let Some(meta) = self.expired.get(hash) {
			return IndexQuery::Expired(meta.priority)
		}
		IndexQuery::Unknown
	}

	fn insert_expired(&mut self, hash: Hash, meta: StatementMeta) {
		self.expired.insert(hash, meta);
	}

	fn is_expired(&self, hash: &Hash) -> bool {
		self.expired.contains_key(hash)
	}

	fn iter(
		&self,
		key: Option<DecryptionKey>,
		topics: &[Topic],
		mut f: impl FnMut(&Hash) -> Result<()>,
	) -> Result<()> {
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
				log::trace!(target: LOG_TARGET, "Iterating: {:?}", HexDisplay::from(h));
				f(h)?
			}
		} else {
			// Start with the smallest topic set or the key set.
			sets[0..num_sets].sort_by_key(|s| s.map_or(0, HashSet::len));
			if let Some(key) = key {
				let key_set =
					if let Some(set) = self.by_dec_key.get(&key) { set } else { return Ok(()) };
				for item in key_set {
					if sets.iter().all(|set| set.unwrap().contains(item)) {
						log::trace!(
							target: LOG_TARGET,
							"Iterating by key: {:?}",
							HexDisplay::from(item)
						);
						f(item)?
					}
				}
			} else {
				for item in sets[0].unwrap() {
					if sets[1..num_sets].iter().all(|set| set.unwrap().contains(item)) {
						log::trace!(
							target: LOG_TARGET,
							"Iterating by topic: {:?}",
							HexDisplay::from(item)
						);
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
			if meta.timestamp + PURGE_AFTER <= current_time {
				purged.push((col::STATEMENTS, hash.to_vec(), None));
				log::trace!(target: LOG_TARGET, "Purged statement {:?}", HexDisplay::from(hash));
				false
			} else {
				true
			}
		});

		// Expire messages.
		let mut num_expired = 0;
		self.entries.retain(|hash, meta| {
			if meta.timestamp + EXPIRE_AFTER <= current_time {
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
				log::trace!(target: LOG_TARGET, "Expired statement {:?}", HexDisplay::from(hash));
				self.expired.insert(hash.clone(), meta.clone());
				num_expired += 1;
				false
			} else {
				true
			}
		});
		if num_expired > 0 {
			// Rebuild the priority queue
			self.by_priority = self
				.entries
				.iter()
				.map(|(hash, meta)| EvictionPriority {
					hash: hash.clone(),
					priority: meta.priority,
					timestamp: meta.timestamp,
				})
				.collect();
		}
		purged
	}

	fn evict(&mut self) -> Vec<(parity_db::ColId, Vec<u8>, Option<Vec<u8>>)> {
		let mut evicted_set = Vec::new();

		while self.by_priority.len() >= self.max_entries {
			if let Some(evicted) = self.by_priority.pop() {
				log::trace!(
					target: LOG_TARGET,
					"Evicting statement {:?}",
					HexDisplay::from(&evicted.hash)
				);
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
				break
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
	) -> Result<Store>
	where
		Block: BlockT,
		Block::Hash: From<BlockHash>,
		Client: ProvideRuntimeApi<Block> + HeaderBackend<Block> + Send + Sync + 'static,
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
				let version = u32::from_le_bytes(
					version
						.try_into()
						.map_err(|_| Error::Db("Error reading database version".into()))?,
				);
				if version != CURRENT_VERSION {
					return Err(Error::Db(format!("Unsupported database version: {version}")))
				}
			},
			None => {
				db.commit([(
					col::META,
					KEY_VERSION.to_vec(),
					Some(CURRENT_VERSION.to_le_bytes().to_vec()),
				)])
				.map_err(|e| Error::Db(e.to_string()))?;
			},
		}

		let mut index = Index::default();
		index.max_entries = MAX_LIVE_STATEMENTS;
		let validator = ClientWrapper { client, _block: Default::default() };
		let validate_fn = Box::new(move |block, source, statement| {
			validator.validate_statement(block, source, statement)
		});

		let store = Store {
			db,
			index: RwLock::new(index),
			validate_fn,
			time_override: None,
			metrics: PrometheusMetrics::new(prometheus),
		};
		store.populate()?;
		Ok(store)
	}

	fn populate(&self) -> Result<()> {
		let current_time = self.timestamp();
		{
			let mut index = self.index.write();
			self.db
				.iter_column_while(col::STATEMENTS, |item| {
					let statement = item.value;
					if let Ok(statement_with_meta) =
						StatementWithMeta::decode(&mut statement.as_slice())
					{
						let hash = statement_with_meta.statement.hash();
						if statement_with_meta.meta.timestamp + EXPIRE_AFTER < current_time {
							log::trace!(
								target: LOG_TARGET,
								"Statement loaded (expired): {:?}",
								HexDisplay::from(&hash)
							);
							index.insert_expired(hash, statement_with_meta.meta);
						} else {
							log::trace!(
								target: LOG_TARGET,
								"Statement loaded {:?}",
								HexDisplay::from(&hash)
							);
							index.insert_with_meta(hash, statement_with_meta);
						}
					}
					true
				})
				.map_err(|e| Error::Db(e.to_string()))?;
		}

		self.maintain();
		Ok(())
	}

	fn collect_statements<R>(
		&self,
		key: Option<DecryptionKey>,
		match_all_topics: &[Topic],
		mut f: impl FnMut(Statement) -> Option<R>,
	) -> Result<Vec<R>> {
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
						log::warn!(
							target: LOG_TARGET,
							"Corrupt statement {:?}",
							HexDisplay::from(hash)
						);
					}
				},
				None => {
					// DB inconsistency
					log::warn!(
						target: LOG_TARGET,
						"Missing statement {:?}",
						HexDisplay::from(hash)
					);
				},
			}
			Ok(())
		})?;
		Ok(result)
	}

	/// Perform periodic store maintenance
	pub fn maintain(&self) {
		log::trace!(target: LOG_TARGET, "Started store maintenance");
		let deleted = self.index.write().maintain(self.timestamp());
		let count = deleted.len() as u64;
		if let Err(e) = self.db.commit(deleted) {
			log::warn!(target: LOG_TARGET, "Error writing to the statement database: {:?}", e);
		} else {
			self.metrics.report(|metrics| metrics.statements_pruned.inc_by(count));
		}
		log::trace!(
			target: LOG_TARGET,
			"Completed store maintenance. Purged: {}, Active: {}, Expired: {}",
			count,
			self.index.read().entries.len(),
			self.index.read().expired.len()
		);
	}

	fn timestamp(&self) -> u64 {
		self.time_override.unwrap_or_else(|| {
			std::time::SystemTime::now()
				.duration_since(std::time::UNIX_EPOCH)
				.unwrap_or_default()
				.as_secs()
		})
	}

	#[cfg(test)]
	fn set_time(&mut self, time: u64) {
		self.time_override = Some(time);
	}
}

impl StatementStore for Store {
	fn dump_encoded(&self) -> Result<Vec<(Hash, Vec<u8>)>> {
		let index = self.index.read();
		let mut result = Vec::with_capacity(index.entries.len());
		for h in self.index.read().entries.keys() {
			let encoded = self.db.get(col::STATEMENTS, h).map_err(|e| Error::Db(e.to_string()))?;
			if let Some(encoded) = encoded {
				if let Ok(entry) = StatementWithMeta::decode(&mut encoded.as_slice()) {
					entry.statement.using_encoded(|statement| {
						let hash = sp_statement_store::hash_encoded(statement);
						if !self.index.read().is_expired(&hash) {
							result.push((hash, entry.statement.encode()));
						}
					});
				}
			}
		}
		Ok(result)
	}

	/// Return all statements.
	fn dump(&self) -> Result<Vec<(Hash, Statement)>> {
		let index = self.index.read();
		let mut result = Vec::with_capacity(index.entries.len());
		for h in self.index.read().entries.keys() {
			let encoded = self.db.get(col::STATEMENTS, h).map_err(|e| Error::Db(e.to_string()))?;
			if let Some(encoded) = encoded {
				if let Ok(entry) = StatementWithMeta::decode(&mut encoded.as_slice()) {
					let hash = entry.statement.hash();
					result.push((hash, entry.statement));
				}
			}
		}
		Ok(result)
	}

	/// Returns a statement by hash.
	fn statement(&self, hash: &Hash) -> Result<Option<Statement>> {
		Ok(
			match self
				.db
				.get(col::STATEMENTS, hash.as_slice())
				.map_err(|e| Error::Db(e.to_string()))?
			{
				Some(entry) => {
					log::trace!(
						target: LOG_TARGET,
						"Queried statement {:?}",
						HexDisplay::from(hash)
					);
					Some(
						StatementWithMeta::decode(&mut entry.as_slice())
							.map_err(|e| Error::Decode(e.to_string()))?
							.statement,
					)
				},
				None => {
					log::trace!(
						target: LOG_TARGET,
						"Queried missing statement {:?}",
						HexDisplay::from(hash)
					);
					None
				},
			},
		)
	}

	/// Return the data of all known statements which include all topics and have no `DecryptionKey`
	/// field.
	fn broadcasts(&self, match_all_topics: &[Topic]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(None, match_all_topics, |statement| statement.into_data())
	}

	/// Return the data of all known statements whose decryption key is identified as `dest` (this
	/// will generally be the public key or a hash thereof for symmetric ciphers, or a hash of the
	/// private key for symmetric ciphers).
	fn posted(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(Some(dest), match_all_topics, |statement| statement.into_data())
	}

	/// Return the decrypted data of all known statements whose decryption key is identified as
	/// `dest`. The key must be available to the client.
	fn posted_clear(&self, match_all_topics: &[Topic], dest: [u8; 32]) -> Result<Vec<Vec<u8>>> {
		self.collect_statements(Some(dest), match_all_topics, |statement| statement.into_data())
	}

	/// Submit a statement to the store. Validates the statement and returns validation result.
	fn submit(&self, statement: Statement, source: StatementSource) -> SubmitResult {
		let hash = statement.hash();
		let priority = match self.index.read().query(&hash) {
			IndexQuery::Expired(priority) => {
				if !source.can_be_resubmitted() {
					return SubmitResult::KnownExpired
				}
				priority
			},
			IndexQuery::Exists(priority) => {
				if !source.can_be_resubmitted() {
					return SubmitResult::Known
				}
				priority
			},
			IndexQuery::Unknown => {
				// Validate.
				let at_block = if let Some(Proof::OnChain { block_hash, .. }) = statement.proof() {
					Some(block_hash.clone())
				} else {
					None
				};
				let validation_result = (self.validate_fn)(at_block, source, statement.clone());
				match validation_result {
					Ok(ValidStatement { priority }) => priority,
					Err(InvalidStatement::BadProof) => {
						log::debug!(
							target: LOG_TARGET,
							"Statement validation failed: BadProof, {:?}",
							statement
						);
						self.metrics.report(|metrics| metrics.validations_invalid.inc());
						return SubmitResult::Bad("Bad statement proof")
					},
					Err(InvalidStatement::NoProof) => {
						log::debug!(
							target: LOG_TARGET,
							"Statement validation failed: NoProof, {:?}",
							statement
						);
						self.metrics.report(|metrics| metrics.validations_invalid.inc());
						return SubmitResult::Bad("Missing statement proof")
					},
					Err(InvalidStatement::InternalError) =>
						return SubmitResult::InternalError(Error::Runtime),
				}
			},
		};

		// Commit to the db prior to locking the index.
		let statement_with_meta = StatementWithMeta {
			meta: StatementMeta { priority, timestamp: self.timestamp() },
			statement,
		};

		let mut commit = self.index.write().evict();
		commit.push((col::STATEMENTS, hash.to_vec(), Some(statement_with_meta.encode())));
		if let Err(e) = self.db.commit(commit) {
			log::debug!(
				target: LOG_TARGET,
				"Statement validation failed: database error {}, {:?}",
				e,
				statement_with_meta.statement
			);
			return SubmitResult::InternalError(Error::Db(e.to_string()))
		}
		self.metrics.report(|metrics| metrics.submitted_statements.inc());
		let mut index = self.index.write();
		index.insert_with_meta(hash, statement_with_meta);
		let network_priority =
			if priority > 0 { NetworkPriority::High } else { NetworkPriority::Low };
		log::trace!(target: LOG_TARGET, "Statement submitted: {:?}", HexDisplay::from(&hash));
		SubmitResult::New(network_priority)
	}

	/// Submit a SCALE-encoded statement.
	fn submit_encoded(&self, mut statement: &[u8], source: StatementSource) -> SubmitResult {
		match Statement::decode(&mut statement) {
			Ok(decoded) => self.submit(decoded, source),
			Err(e) => {
				log::debug!(
					target: LOG_TARGET,
					"Error decoding submitted statement. Failed with: {}",
					e
				);
				SubmitResult::Bad("Bad SCALE encoding")
			},
		}
	}
}

#[cfg(test)]
mod tests {
	use crate::Store;
	use sp_core::Pair;
	use sp_statement_store::{
		runtime_api::{InvalidStatement, ValidStatement, ValidateStatement},
		NetworkPriority, Proof, SignatureVerificationResult, Statement, StatementSource,
		StatementStore, SubmitResult, Topic,
	};

	type Extrinsic = sp_runtime::OpaqueExtrinsic;
	type Hash = sp_core::H256;
	type Hashing = sp_runtime::traits::BlakeTwo256;
	type BlockNumber = u64;
	type Header = sp_runtime::generic::Header<BlockNumber, Hashing>;
	type Block = sp_runtime::generic::Block<Header, Extrinsic>;

	const CORRECT_BLOCK_HASH: [u8; 32] = [1u8; 32];

	#[derive(Clone)]
	pub(crate) struct TestClient;

	pub(crate) struct RuntimeApi {
		_inner: TestClient,
	}

	impl sp_api::ProvideRuntimeApi<Block> for TestClient {
		type Api = RuntimeApi;
		fn runtime_api(&self) -> sp_api::ApiRef<Self::Api> {
			RuntimeApi { _inner: self.clone() }.into()
		}
	}
	sp_api::mock_impl_runtime_apis! {
		impl ValidateStatement<Block> for RuntimeApi {
			fn validate_statement(
				_source: StatementSource,
				statement: Statement,
			) -> std::result::Result<ValidStatement, InvalidStatement> {
				match statement.verify_signature() {
					SignatureVerificationResult::Valid(_) => Ok(ValidStatement{priority: 10}),
					SignatureVerificationResult::Invalid => Err(InvalidStatement::BadProof),
					SignatureVerificationResult::NoSignature => {
						if let Some(Proof::OnChain { block_hash, .. }) = statement.proof() {
							if block_hash == &CORRECT_BLOCK_HASH {
								Ok(ValidStatement{priority: 1})
							} else {
								Err(InvalidStatement::BadProof)
							}
						} else {
							Ok(ValidStatement{priority: 0})
						}
					}
				}
			}
		}
	}

	impl sp_blockchain::HeaderBackend<Block> for TestClient {
		fn header(&self, _hash: Hash) -> sp_blockchain::Result<Option<Header>> {
			unimplemented!()
		}
		fn info(&self) -> sp_blockchain::Info<Block> {
			sp_blockchain::Info {
				best_hash: CORRECT_BLOCK_HASH.into(),
				best_number: 0,
				genesis_hash: Default::default(),
				finalized_hash: CORRECT_BLOCK_HASH.into(),
				finalized_number: 1,
				finalized_state: None,
				number_leaves: 0,
				block_gap: None,
			}
		}
		fn status(&self, _hash: Hash) -> sp_blockchain::Result<sp_blockchain::BlockStatus> {
			unimplemented!()
		}
		fn number(&self, _hash: Hash) -> sp_blockchain::Result<Option<BlockNumber>> {
			unimplemented!()
		}
		fn hash(&self, _number: BlockNumber) -> sp_blockchain::Result<Option<Hash>> {
			unimplemented!()
		}
	}

	fn test_store() -> (Store, tempfile::TempDir) {
		let _ = env_logger::try_init();
		let temp_dir = tempfile::Builder::new().tempdir().expect("Error creating test dir");

		let client = std::sync::Arc::new(TestClient);
		let mut path: std::path::PathBuf = temp_dir.path().into();
		path.push("db");
		let store = Store::new(&path, client, None).unwrap();
		(store, temp_dir) // return order is important. Store must be dropped before TempDir
	}

	fn signed_statement(data: u8) -> Statement {
		signed_statement_with_topics(data, &[])
	}

	fn signed_statement_with_topics(data: u8, topics: &[Topic]) -> Statement {
		let mut statement = Statement::new();
		statement.set_plain_data(vec![data]);
		for i in 0..topics.len() {
			statement.set_topic(i, topics[i].clone());
		}
		let kp = sp_core::ed25519::Pair::from_string("//Alice", None).unwrap();
		statement.sign_ed25519_private(&kp);
		statement
	}

	fn onchain_statement_with_topics(data: u8, topics: &[Topic]) -> Statement {
		let mut statement = Statement::new();
		statement.set_plain_data(vec![data]);
		for i in 0..topics.len() {
			statement.set_topic(i, topics[i].clone());
		}
		statement.set_proof(Proof::OnChain {
			block_hash: CORRECT_BLOCK_HASH,
			who: Default::default(),
			event_index: 0,
		});
		statement
	}

	fn topic(data: u64) -> Topic {
		let mut topic: Topic = Default::default();
		topic[0..8].copy_from_slice(&data.to_le_bytes());
		topic
	}

	#[test]
	fn submit_one() {
		let (store, _temp) = test_store();
		let statement0 = signed_statement(0);
		assert_eq!(
			store.submit(statement0, StatementSource::Network),
			SubmitResult::New(NetworkPriority::High)
		);
		let unsigned = Statement::new();
		assert_eq!(
			store.submit(unsigned, StatementSource::Network),
			SubmitResult::New(NetworkPriority::Low)
		);
	}

	#[test]
	fn save_and_load_statements() {
		let (store, temp) = test_store();
		let statement0 = signed_statement(0);
		let statement1 = signed_statement(1);
		let statement2 = signed_statement(2);
		assert_eq!(
			store.submit(statement0.clone(), StatementSource::Network),
			SubmitResult::New(NetworkPriority::High)
		);
		assert_eq!(
			store.submit(statement1.clone(), StatementSource::Network),
			SubmitResult::New(NetworkPriority::High)
		);
		assert_eq!(
			store.submit(statement2.clone(), StatementSource::Network),
			SubmitResult::New(NetworkPriority::High)
		);
		assert_eq!(store.dump().unwrap().len(), 3);
		assert_eq!(store.broadcasts(&[]).unwrap().len(), 3);
		assert_eq!(store.statement(&statement1.hash()).unwrap(), Some(statement1.clone()));
		drop(store);

		let client = std::sync::Arc::new(TestClient);
		let mut path: std::path::PathBuf = temp.path().into();
		path.push("db");
		let store = Store::new(&path, client, None).unwrap();
		assert_eq!(store.dump().unwrap().len(), 3);
		assert_eq!(store.broadcasts(&[]).unwrap().len(), 3);
		assert_eq!(store.statement(&statement1.hash()).unwrap(), Some(statement1));
	}

	#[test]
	fn search_by_topic() {
		let (store, _temp) = test_store();
		let statement0 = signed_statement(0);
		let statement1 = signed_statement_with_topics(1, &[topic(0)]);
		let statement2 = signed_statement_with_topics(2, &[topic(0), topic(1)]);
		let statement3 = signed_statement_with_topics(3, &[topic(0), topic(1), topic(2)]);
		let statement4 =
			signed_statement_with_topics(4, &[topic(0), topic(42), topic(2), topic(3)]);
		let statements = vec![statement0, statement1, statement2, statement3, statement4];
		for s in &statements {
			store.submit(s.clone(), StatementSource::Network);
		}

		let assert_topics = |topics: &[u64], expected: &[u8]| {
			let topics: Vec<_> = topics.iter().map(|t| topic(*t)).collect();
			let mut got_vals: Vec<_> =
				store.broadcasts(&topics).unwrap().into_iter().map(|d| d[0]).collect();
			got_vals.sort();
			assert_eq!(expected.to_vec(), got_vals);
		};

		assert_topics(&[], &[0, 1, 2, 3, 4]);
		assert_topics(&[0], &[1, 2, 3, 4]);
		assert_topics(&[1], &[2, 3]);
		assert_topics(&[2], &[3, 4]);
		assert_topics(&[3], &[4]);
		assert_topics(&[42], &[4]);

		assert_topics(&[0, 1], &[2, 3]);
		assert_topics(&[1, 2], &[3]);
	}

	#[test]
	fn maintenance() {
		use super::{EXPIRE_AFTER, MAX_LIVE_STATEMENTS, PURGE_AFTER};
		// Check test assumptions
		assert!((MAX_LIVE_STATEMENTS as u64) < EXPIRE_AFTER);

		// first 10 statements are high priority, the rest is low.
		let (mut store, _temp) = test_store();
		for time in 0..MAX_LIVE_STATEMENTS as u64 {
			store.set_time(time);
			let statement = if time < 10 {
				signed_statement_with_topics(0, &[topic(time)])
			} else {
				onchain_statement_with_topics(0, &[topic(time)])
			};
			store.submit(statement, StatementSource::Network);
		}

		let first = signed_statement_with_topics(0, &[topic(0)]);
		let second = signed_statement_with_topics(0, &[topic(0)]);
		assert_eq!(first, second);
		assert_eq!(store.statement(&first.hash()).unwrap().unwrap(), first);
		assert_eq!(store.index.read().entries.len(), MAX_LIVE_STATEMENTS);

		let first_to_be_evicted = onchain_statement_with_topics(0, &[topic(10)]);
		assert_eq!(store.index.read().entries.len(), MAX_LIVE_STATEMENTS);
		assert_eq!(
			store.statement(&first_to_be_evicted.hash()).unwrap().unwrap(),
			first_to_be_evicted
		);

		// Check that the new statement replaces the old.
		store.submit(
			signed_statement_with_topics(0, &[topic(MAX_LIVE_STATEMENTS as u64 + 1)]),
			StatementSource::Network,
		);
		assert_eq!(store.statement(&first_to_be_evicted.hash()).unwrap(), None);

		store.set_time(EXPIRE_AFTER + (MAX_LIVE_STATEMENTS as u64) / 2);
		store.maintain();
		// Half statements should be expired.
		assert_eq!(store.index.read().entries.len(), MAX_LIVE_STATEMENTS / 2);
		assert_eq!(store.index.read().expired.len(), MAX_LIVE_STATEMENTS / 2);

		// The high-priority statement should survive.
		assert_eq!(store.statement(&first.hash()).unwrap().unwrap(), first);

		store.set_time(PURGE_AFTER + (MAX_LIVE_STATEMENTS as u64) / 2);
		store.maintain();
		assert_eq!(store.index.read().entries.len(), 0);
		assert_eq!(store.index.read().expired.len(), MAX_LIVE_STATEMENTS / 2);
	}
}
