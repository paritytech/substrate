// Copyright 2018 Parity Technologies (UK) Ltd.
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

use std::{
	collections::HashMap,
	marker::PhantomData,
	sync::{Arc, Weak},
};

use futures::sync::mpsc;
use parking_lot::{RwLock, Mutex};
use txpool;
use primitives::{Hash, block::Extrinsic};

use listener::Listener;
use watcher::Watcher;

/// Extrinsics pool.
pub struct Pool<V, S, E> where
	V: txpool::Verifier<Extrinsic>,
	S: txpool::Scoring<V::VerifiedTransaction>,
{
	_error: Mutex<PhantomData<E>>,
	pool: RwLock<txpool::Pool<
		V::VerifiedTransaction,
		S,
		Listener,
	>>,
	verifier: V,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<Weak<V::VerifiedTransaction>>>>,
}

impl<V, S, E> Pool<V, S, E> where
	V: txpool::Verifier<Extrinsic>,
	S: txpool::Scoring<V::VerifiedTransaction>,
	V::VerifiedTransaction: txpool::VerifiedTransaction<Hash=Hash>,
	E: From<V::Error>,
	E: From<txpool::Error>,
{
	/// Create a new transaction pool.
	pub fn new(options: txpool::Options, verifier: V, scoring: S) -> Self {
		Pool {
			_error: Default::default(),
			pool: RwLock::new(txpool::Pool::new(Listener::default(), scoring, options)),
			verifier,
			import_notification_sinks: Default::default(),
		}
	}

	/// Imports a pre-verified extrinsic to the pool.
	pub fn import(&self, xt: V::VerifiedTransaction) -> Result<Arc<V::VerifiedTransaction>, E> {
		let result = self.pool.write().import(xt)?;

		let weak = Arc::downgrade(&result);
		self.import_notification_sinks.lock()
			.retain(|sink| sink.unbounded_send(weak.clone()).is_ok());

		Ok(result)
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> mpsc::UnboundedReceiver<Weak<V::VerifiedTransaction>> {
		let (sink, stream) = mpsc::unbounded();
		self.import_notification_sinks.lock().push(sink);
		stream
	}

	/// Invoked when extrinsics are broadcasted.
	pub fn on_broadcasted(&self, propagated: HashMap<Hash, Vec<String>>) {
		for (hash, peers) in propagated.into_iter() {
			self.pool.write().listener_mut().broadcasted(&hash, peers);
		}
	}

	/// Imports a bunch of extrinsics to the pool
	pub fn submit(&self, xts: Vec<Extrinsic>) -> Result<Vec<Arc<V::VerifiedTransaction>>, E> {
		xts
			.into_iter()
			.map(|xt| self.verifier.verify_transaction(xt))
			.map(|xt| {
				Ok(self.pool.write().import(xt?)?)
			})
			.collect()
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch(&self, xt: Extrinsic) -> Result<Watcher, E> {
		let xt = self.submit(vec![xt])?.pop().expect("One extrinsic passed; one result returned; qed");
		Ok(self.pool.write().listener_mut().create_watcher(xt))
	}

	/// Remove from the pool.
	pub fn remove(&self, hashes: &[Hash], is_valid: bool) -> Vec<Option<Arc<V::VerifiedTransaction>>> {
		let mut pool = self.pool.write();
		let mut results = Vec::with_capacity(hashes.len());
		for hash in hashes {
			results.push(pool.remove(hash, is_valid));
		}
		results
	}

	/// Cull transactions from the queue.
	pub fn cull<R>(&self, senders: Option<&[<V::VerifiedTransaction as txpool::VerifiedTransaction>::Sender]>, ready: R) -> usize where
		R: txpool::Ready<V::VerifiedTransaction>,
	{
		self.pool.write().cull(senders, ready)
	}

	/// Cull transactions from the queue and then compute the pending set.
	pub fn cull_and_get_pending<R, F, T>(&self, ready: R, f: F) -> T where
		R: txpool::Ready<V::VerifiedTransaction> + Clone,
		F: FnOnce(txpool::PendingIterator<V::VerifiedTransaction, R, S, Listener>) -> T,
	{
		let mut pool = self.pool.write();
		pool.cull(None, ready.clone());
		f(pool.pending(ready))
	}

	/// Get the full status of the queue (including readiness)
	pub fn status<R: txpool::Ready<V::VerifiedTransaction>>(&self, ready: R) -> txpool::Status {
		self.pool.read().status(ready)
	}

	/// Returns light status of the pool.
	pub fn light_status(&self) -> txpool::LightStatus {
		self.pool.read().light_status()
	}
}
