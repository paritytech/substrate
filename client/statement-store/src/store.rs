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

use std::{collections::{HashSet, HashMap}, sync::Arc};

use parking_lot::RwLock;
use sp_statement_store::{Statement, Topic, DecryptionKey, Result, Error, Hash, BlockHash, SubmitResult, NetworkPriority};
use sp_statement_store::runtime_api::{ValidateStatement, ValidStatement, InvalidStatement, StatementSource};
use sp_core::{Encode, Decode};
use sp_api::ProvideRuntimeApi;
use sp_runtime::traits::Block as BlockT;

const KEY_VERSION: &[u8] = b"version".as_slice();
const CURRENT_VERSION: u32 = 1;

const LOG_TARGET: &str = "statement";

mod col {
	pub const META: u8 = 0;
	pub const STATEMENTS: u8 = 1;
	pub const COUNT: u8 = 2;
}

#[derive(Default)]
struct Index {
	by_topic: HashMap<Topic, HashSet<Hash>>,
	by_dec_key: HashMap<DecryptionKey, HashSet<Hash>>,
	extended_topics: HashMap<Hash, [Topic; 3]>,
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
}

impl Index {
	fn insert(&mut self, hash: Hash, statement: Statement) {
		let mut ext_topics = [Topic::default(); 3];
		let mut nt = 0;
		while let Some(t) = statement.topic(nt) {
			if nt == 0 {
				self.by_topic.entry(t).or_default().insert(hash);
			} else {
				ext_topics[nt - 1] = t;
			}
			nt += 1;
		}
		self.extended_topics.insert(hash, ext_topics);
		if let Some(key) = statement.decryption_key() {
			self.by_dec_key.entry(key).or_default().insert(hash);
		}
	}

	fn iter_topics(&self, key: Option<DecryptionKey>, topics: &[Topic], mut f: impl FnMut(&Hash) -> Result<()>) -> Result<()> {
		let mut sets: [Option<&HashSet<Hash>>; 4] = Default::default();
		let mut num_sets = 0;
		for t in topics {
			sets[num_sets] = self.by_topic.get(t);
			if sets[num_sets].is_some() {
				num_sets += 1;
			}
		}
		if num_sets == 0 && key.is_none() {
			return Ok(());
		}
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
		Ok(())
	}
}

impl Store {
	/// Create a new shared store instance. There should only be one per process.
	pub fn new<Block, Client>(path: &std::path::Path, client: Arc<Client>) -> Result<Arc<Store>>
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

		let mut index = Index::default();
		db.iter_column_while(col::STATEMENTS, |item| {
			let statement = item.value;
			let hash = sp_statement_store::hash_encoded(&statement);
			if let Ok(statement) = Statement::decode(&mut statement.as_slice()) {
				index.insert(hash, statement);
			}
			true
		}).map_err(|e| Error::Db(e.to_string()))?;

		let validator = ClientWrapper { client, _block: Default::default() };
		let validate_fn = Box::new(move |block, source, statement| validator.validate_statement(block, source, statement));

		Ok(Arc::new(Store {
			db,
			index: RwLock::new(index),
			validate_fn,
		}))
	}

	fn collect_statements<R>(&self, key: Option<DecryptionKey>, match_all_topics: &[Topic], mut f: impl FnMut(Statement) -> Option<R> ) -> Result<Vec<R>> {
		let mut result = Vec::new();
		let index = self.index.read();
		index.iter_topics(key, match_all_topics, |hash| {
			match self.db.get(col::STATEMENTS, hash).map_err(|e| Error::Db(e.to_string()))? {
				Some(statement) => {
					if let Ok(statement) = Statement::decode(&mut statement.as_slice()) {
						if let Some(data) = f(statement) {
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
	pub async fn maintain(&self) {
	}
}

impl sp_statement_store::StatementStore for Store {
	fn dump_encoded(&self) -> Result<Vec<(Hash, Vec<u8>)>> {
		let mut result = Vec::new();
		self.db.iter_column_while(col::STATEMENTS, |item| {
			result.push((sp_statement_store::hash_encoded(&item.value), item.value));
			true
		}).map_err(|e| Error::Db(e.to_string()))?;
		Ok(result)
	}

	/// Return all statements.
	fn dump(&self) -> Result<Vec<(Hash, Statement)>> {
		let mut result = Vec::new();
		self.db.iter_column_while(col::STATEMENTS, |item| {
			if let Ok(statement) = Statement::decode(&mut item.value.as_slice()) {
				result.push((statement.hash(), statement));
			}
			true
		}).map_err(|e| Error::Db(e.to_string()))?;
		Ok(result)
	}

	fn statement(&self, hash: &Hash) -> Result<Option<Statement>> {
		Ok(match self.db.get(col::STATEMENTS, hash.as_slice()).map_err(|e| Error::Db(e.to_string()))? {
			Some(statement) => {
				Some(Statement::decode(&mut statement.as_slice()).map_err(|e| Error::Decode(e.to_string()))?)
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

	/// Submit a statement.
	fn submit(&self, statement: Statement) -> SubmitResult {
		let encoded = statement.encode();
		let hash = sp_statement_store::hash_encoded(&encoded);
		let validation_result = (self.validate_fn)(Default::default(), StatementSource::Local, statement.clone());
		match validation_result {
			Ok(ValidStatement { priority }) => {
				//commit to the db with locked index
				let mut index = self.index.write();
				if let Err(e) = self.db.commit([(col::STATEMENTS, &hash, Some(encoded))]) {
					log::debug!(target: LOG_TARGET, "Statement validation failed: database error {}, {:?}", e, statement);
					return SubmitResult::InternalError(Error::Db(e.to_string()));
				}
				index.insert(hash, statement);
				let network_priority = if priority > 0 { NetworkPriority::High } else { NetworkPriority::Low };
				SubmitResult::OkNew(network_priority)
			}
			Err(InvalidStatement::BadProof) => {
				log::debug!(target: LOG_TARGET, "Statement validation failed: BadProof, {:?}", statement);
				SubmitResult::Bad("Bad statement proof")
			},
			Err(InvalidStatement::NoProof) =>{
				log::debug!(target: LOG_TARGET, "Statement validation failed: NoProof, {:?}", statement);
				SubmitResult::Bad("Missing statement proof")
			},
			Err(InvalidStatement::InternalError) => SubmitResult::InternalError(Error::Runtime),
		}
	}

	/// Submit a SCALE-encoded statement.
	fn submit_encoded(&self, mut statement: &[u8]) -> SubmitResult {
		match Statement::decode(&mut statement) {
			Ok(decoded) => self.submit(decoded),
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

