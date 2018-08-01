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

//! Statement routing and consensus table router implementation.
//!
//! During the consensus process, validators exchange statements on validity and availability
//! of parachain candidates.
//! The `Router` in this file hooks into the underlying network to fulfill
//! the `TableRouter` trait from `polkadot-consensus`, which is expected to call into a shared statement table
//! and dispatch evaluation work as necessary when new statements come in.

use polkadot_api::{PolkadotApi, LocalPolkadotApi};
use polkadot_consensus::{SharedTable, TableRouter, SignedStatement, GenericStatement, StatementProducer};
use polkadot_primitives::{Hash, BlockId, SessionKey};
use polkadot_primitives::parachain::{BlockData, Extrinsic, CandidateReceipt};

use futures::prelude::*;
use tokio::runtime::TaskExecutor;
use parking_lot::Mutex;

use std::collections::{HashMap, HashSet};
use std::io;
use std::sync::Arc;

use super::{NetworkService, Knowledge};

/// Table routing implementation.
pub struct Router<P: PolkadotApi> {
	table: Arc<SharedTable>,
	network: Arc<NetworkService>,
	api: Arc<P>,
	task_executor: TaskExecutor,
	parent_hash: Hash,
	knowledge: Arc<Mutex<Knowledge>>,
	deferred_statements: Arc<Mutex<DeferredStatements>>,
}

impl<P: PolkadotApi> Router<P> {
	pub(crate) fn new(
		table: Arc<SharedTable>,
		network: Arc<NetworkService>,
		api: Arc<P>,
		task_executor: TaskExecutor,
		parent_hash: Hash,
		knowledge: Arc<Mutex<Knowledge>>,
	) -> Self {
		Router {
			table,
			network,
			api,
			task_executor,
			parent_hash,
			knowledge,
			deferred_statements: Arc::new(Mutex::new(DeferredStatements::new())),
		}
	}

	pub(crate) fn session_key(&self) -> SessionKey {
		self.table.session_key()
	}
}

impl<P: PolkadotApi> Clone for Router<P> {
	fn clone(&self) -> Self {
		Router {
			table: self.table.clone(),
			network: self.network.clone(),
			api: self.api.clone(),
			task_executor: self.task_executor.clone(),
			parent_hash: self.parent_hash.clone(),
			deferred_statements: self.deferred_statements.clone(),
			knowledge: self.knowledge.clone(),
		}
	}
}

impl<P: LocalPolkadotApi + Send + Sync + 'static> Router<P> {
	/// Import a statement whose signature has been checked already.
	pub(crate) fn import_statement(&self, statement: SignedStatement) {
		trace!(target: "p_net", "importing consensus statement {:?}", statement.statement);

		// defer any statements for which we haven't imported the candidate yet
		let c_hash = {
			let candidate_data = match statement.statement {
				GenericStatement::Candidate(ref c) => Some(c.hash()),
				GenericStatement::Valid(ref hash)
					| GenericStatement::Invalid(ref hash)
					| GenericStatement::Available(ref hash)
					=> self.table.with_candidate(hash, |c| c.map(|_| *hash)),
			};
			match candidate_data {
				Some(x) => x,
				None => {
					self.deferred_statements.lock().push(statement);
					return;
				}
			}
		};

		// import all statements pending on this candidate
		let (mut statements, _traces) = if let GenericStatement::Candidate(_) = statement.statement {
			self.deferred_statements.lock().get_deferred(&c_hash)
		} else {
			(Vec::new(), Vec::new())
		};

		// prepend the candidate statement.
		debug!(target: "consensus", "Importing statements about candidate {:?}", c_hash);
		statements.insert(0, statement);
		let producers: Vec<_> = self.table.import_remote_statements(
			self,
			statements.iter().cloned(),
		);
		// dispatch future work as necessary.
		for (producer, statement) in producers.into_iter().zip(statements) {
			self.knowledge.lock().note_statement(statement.sender, &statement.statement);

			if let Some(producer) = producer {
				trace!(target: "consensus", "driving statement work to completion");
				self.dispatch_work(c_hash, producer);
			}
		}
	}

	fn dispatch_work<D, E>(&self, candidate_hash: Hash, producer: StatementProducer<D, E>) where
		D: Future<Item=BlockData,Error=io::Error> + Send + 'static,
		E: Future<Item=Extrinsic,Error=io::Error> + Send + 'static,
	{
		let parent_hash = self.parent_hash.clone();

		let api = self.api.clone();
		let validate = move |collation| -> Option<bool> {
			let id = BlockId::hash(parent_hash);
			match ::polkadot_consensus::validate_collation(&*api, &id, &collation) {
				Ok(()) => Some(true),
				Err(e) => {
					debug!(target: "p_net", "Encountered bad collation: {}", e);
					Some(false)
				}
			}
		};

		let table = self.table.clone();
		let network = self.network.clone();
		let knowledge = self.knowledge.clone();

		let work = producer.prime(validate)
			.map(move |produced| {
				// store the data before broadcasting statements, so other peers can fetch.
				knowledge.lock().note_candidate(
					candidate_hash,
					produced.block_data,
					produced.extrinsic
				);

				// propagate the statements
				if let Some(validity) = produced.validity {
					let signed = table.sign_and_import(validity.clone()).0;
					network.with_spec(|spec, ctx| spec.gossip_statement(ctx, parent_hash, signed));
				}

				if let Some(availability) = produced.availability {
					let signed = table.sign_and_import(availability).0;
					network.with_spec(|spec, ctx| spec.gossip_statement(ctx, parent_hash, signed));
				}
			})
			.map_err(|e| debug!(target: "p_net", "Failed to produce statements: {:?}", e));

		self.task_executor.spawn(work);
	}
}

impl<P: LocalPolkadotApi + Send> TableRouter for Router<P> {
	type Error = io::Error;
	type FetchCandidate = BlockDataReceiver;
	type FetchExtrinsic = Result<Extrinsic, Self::Error>;

	fn local_candidate(&self, receipt: CandidateReceipt, block_data: BlockData, extrinsic: Extrinsic) {
		// give to network to make available.
		let hash = receipt.hash();
		let (candidate, availability) = self.table.sign_and_import(GenericStatement::Candidate(receipt));

		self.knowledge.lock().note_candidate(hash, Some(block_data), Some(extrinsic));
		self.network.with_spec(|spec, ctx| {
			spec.gossip_statement(ctx, self.parent_hash, candidate);
			if let Some(availability) = availability {
				spec.gossip_statement(ctx, self.parent_hash, availability);
			}
		});
	}

	fn fetch_block_data(&self, candidate: &CandidateReceipt) -> BlockDataReceiver {
		let parent_hash = self.parent_hash;
		let rx = self.network.with_spec(|spec, ctx| { spec.fetch_block_data(ctx, candidate, parent_hash) });
		BlockDataReceiver { inner: rx }
	}

	fn fetch_extrinsic_data(&self, _candidate: &CandidateReceipt) -> Self::FetchExtrinsic {
		Ok(Extrinsic)
	}
}

/// Receiver for block data.
pub struct BlockDataReceiver {
	inner: Option<::futures::sync::oneshot::Receiver<BlockData>>,
}

impl Future for BlockDataReceiver {
	type Item = BlockData;
	type Error = io::Error;

	fn poll(&mut self) -> Poll<BlockData, io::Error> {
		match self.inner {
			Some(ref mut inner) => inner.poll().map_err(|_| io::Error::new(
				io::ErrorKind::Other,
				"Sending end of channel hung up",
			)),
			None => return Err(io::Error::new(
				io::ErrorKind::Other,
				"Network service is unavailable",
			)),
		}
	}
}

// A unique trace for valid statements issued by a validator.
#[derive(Hash, PartialEq, Eq, Clone, Debug)]
enum StatementTrace {
	Valid(SessionKey, Hash),
	Invalid(SessionKey, Hash),
	Available(SessionKey, Hash),
}

// helper for deferring statements whose associated candidate is unknown.
struct DeferredStatements {
	deferred: HashMap<Hash, Vec<SignedStatement>>,
	known_traces: HashSet<StatementTrace>,
}

impl DeferredStatements {
	fn new() -> Self {
		DeferredStatements {
			deferred: HashMap::new(),
			known_traces: HashSet::new(),
		}
	}

	fn push(&mut self, statement: SignedStatement) {
		let (hash, trace) = match statement.statement {
			GenericStatement::Candidate(_) => return,
			GenericStatement::Valid(hash) => (hash, StatementTrace::Valid(statement.sender, hash)),
			GenericStatement::Invalid(hash) => (hash, StatementTrace::Invalid(statement.sender, hash)),
			GenericStatement::Available(hash) => (hash, StatementTrace::Available(statement.sender, hash)),
		};

		if self.known_traces.insert(trace) {
			self.deferred.entry(hash).or_insert_with(Vec::new).push(statement);
		}
	}

	fn get_deferred(&mut self, hash: &Hash) -> (Vec<SignedStatement>, Vec<StatementTrace>) {
		match self.deferred.remove(hash) {
			None => (Vec::new(), Vec::new()),
			Some(deferred) => {
				let mut traces = Vec::new();
				for statement in deferred.iter() {
					let trace = match statement.statement {
						GenericStatement::Candidate(_) => continue,
						GenericStatement::Valid(hash) => StatementTrace::Valid(statement.sender, hash),
						GenericStatement::Invalid(hash) => StatementTrace::Invalid(statement.sender, hash),
						GenericStatement::Available(hash) => StatementTrace::Available(statement.sender, hash),
					};

					self.known_traces.remove(&trace);
					traces.push(trace);
				}

				(deferred, traces)
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use substrate_primitives::H512;

	#[test]
	fn deferred_statements_works() {
		let mut deferred = DeferredStatements::new();
		let hash = [1; 32].into();
		let sig = H512([2; 64]).into();
		let sender = [255; 32].into();

		let statement = SignedStatement {
			statement: GenericStatement::Valid(hash),
			sender,
			signature: sig,
		};

		// pre-push.
		{
			let (signed, traces) = deferred.get_deferred(&hash);
			assert!(signed.is_empty());
			assert!(traces.is_empty());
		}

		deferred.push(statement.clone());
		deferred.push(statement.clone());

		// draining: second push should have been ignored.
		{
			let (signed, traces) = deferred.get_deferred(&hash);
			assert_eq!(signed.len(), 1);

			assert_eq!(traces.len(), 1);
			assert_eq!(signed[0].clone(), statement);
			assert_eq!(traces[0].clone(), StatementTrace::Valid(sender, hash));
		}

		// after draining
		{
			let (signed, traces) = deferred.get_deferred(&hash);
			assert!(signed.is_empty());
			assert!(traces.is_empty());
		}
	}
}
