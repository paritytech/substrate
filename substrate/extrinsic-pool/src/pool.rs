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
	fmt,
	marker::PhantomData,
	sync::Arc,
};

use futures::sync::mpsc;
use parking_lot::{RwLock, Mutex};
use txpool;

use listener::Listener;
use watcher::Watcher;

/// Extrinsics pool.
pub struct Pool<Hash, VEx, S, E> where
	Hash: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex,
	S: txpool::Scoring<VEx>,
	VEx: txpool::VerifiedTransaction<Hash=Hash>,
{
	_error: Mutex<PhantomData<E>>,
	pool: RwLock<txpool::Pool<
		VEx,
		S,
		Listener<Hash>,
	>>,
	import_notification_sinks: Mutex<Vec<mpsc::UnboundedSender<()>>>,
}

impl<Hash, VEx, S, E> Pool<Hash, VEx, S, E> where
	Hash: ::std::hash::Hash + Eq + Copy + fmt::Debug + fmt::LowerHex + Default,
	S: txpool::Scoring<VEx>,
	VEx: txpool::VerifiedTransaction<Hash=Hash>,
	E: From<txpool::Error>,
{
	/// Create a new transaction pool.
	pub fn new(options: txpool::Options, scoring: S) -> Self {
		Pool {
			_error: Default::default(),
			pool: RwLock::new(txpool::Pool::new(Listener::default(), scoring, options)),
			import_notification_sinks: Default::default(),
		}
	}

	/// Imports a pre-verified extrinsic to the pool.
	pub fn import(&self, xt: VEx) -> Result<Arc<VEx>, E> {
		let result = self.pool.write().import(xt)?;

		self.import_notification_sinks.lock()
			.retain(|sink| sink.unbounded_send(()).is_ok());

		Ok(result)
	}

	/// Return an event stream of transactions imported to the pool.
	pub fn import_notification_stream(&self) -> mpsc::UnboundedReceiver<()> {
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

	/// Imports a bunch of unverified extrinsics to the pool
	pub fn submit<V, Ex, T>(&self, verifier: V, xts: T) -> Result<Vec<Arc<VEx>>, E> where
		V: txpool::Verifier<Ex, VerifiedTransaction=VEx>,
		E: From<V::Error>,
		T: IntoIterator<Item=Ex>
	{
		xts
			.into_iter()
			.map(|xt| verifier.verify_transaction(xt))
			.map(|xt| {
				Ok(self.pool.write().import(xt?)?)
			})
			.collect()
	}

	/// Import a single extrinsic and starts to watch their progress in the pool.
	pub fn submit_and_watch<V, Ex>(&self, verifier: V, xt: Ex) -> Result<Watcher<Hash>, E> where
		V: txpool::Verifier<Ex, VerifiedTransaction=VEx>,
		E: From<V::Error>,
	{
		let xt = self.submit(verifier, vec![xt])?.pop().expect("One extrinsic passed; one result returned; qed");
		Ok(self.pool.write().listener_mut().create_watcher(xt))
	}

	/// Remove from the pool.
	pub fn remove(&self, hashes: &[Hash], is_valid: bool) -> Vec<Option<Arc<VEx>>> {
		let mut pool = self.pool.write();
		let mut results = Vec::with_capacity(hashes.len());
		for hash in hashes {
			results.push(pool.remove(hash, !is_valid));
		}
		results
	}

	/// Cull transactions from the queue.
	pub fn cull<R>(&self, senders: Option<&[<VEx as txpool::VerifiedTransaction>::Sender]>, ready: R) -> usize where
		R: txpool::Ready<VEx>,
	{
		self.pool.write().cull(senders, ready)
	}

	/// Get the full status of the queue (including readiness)
	pub fn status<R: txpool::Ready<VEx>>(&self, ready: R) -> txpool::Status {
		self.pool.read().status(ready)
	}

	/// Returns light status of the pool.
	pub fn light_status(&self) -> txpool::LightStatus {
		self.pool.read().light_status()
	}

	/// Removes all transactions from given sender
	pub fn remove_sender(&self, sender: VEx::Sender) -> Vec<Arc<VEx>> {
		let mut pool = self.pool.write();
		let pending = pool.pending_from_sender(|_: &VEx| txpool::Readiness::Ready, &sender).collect();
		// remove all transactions from this sender
		pool.cull(Some(&[sender]), |_: &VEx| txpool::Readiness::Stale);
		pending
	}

	/// Retrieve the pending set. Be careful to not leak the pool `ReadGuard` to prevent deadlocks.
	pub fn pending<R, F, T>(&self, ready: R, f: F) -> T where
		R: txpool::Ready<VEx>,
		F: FnOnce(txpool::PendingIterator<VEx, R, S, Listener<Hash>>) -> T,
	{
		f(self.pool.read().pending(ready))
	}

	/// Retrieve all transactions in the pool. The transactions might be unordered.
	pub fn all<F, T>(&self, f: F) -> T where
		F: FnOnce(txpool::UnorderedIterator<VEx, AlwaysReady, S>) -> T,
	{
		f(self.pool.read().unordered_pending(AlwaysReady))
	}
}

/// A Readiness implementation that returns `Ready` for all transactions.
pub struct AlwaysReady;
impl<VEx> txpool::Ready<VEx> for AlwaysReady {
	fn is_ready(&mut self, _tx: &VEx) -> txpool::Readiness {
		txpool::Readiness::Ready
	}
}
