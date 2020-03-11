// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

use std::collections::HashMap;
use std::sync::{Arc, atomic::{self, AtomicUsize}};

use log::{error, warn};
use jsonrpc_pubsub::{SubscriptionId, typed::{Sink, Subscriber}};
use parking_lot::Mutex;
use jsonrpc_core::futures::sync::oneshot;
use jsonrpc_core::futures::{Future, future};

type Id = u64;

/// Alias for a an implementation of `futures::future::Executor`.
pub type TaskExecutor = Arc<dyn future::Executor<Box<dyn Future<Item = (), Error = ()> + Send>> + Send + Sync>;

/// Generate unique ids for subscriptions.
#[derive(Clone, Debug)]
pub struct IdProvider {
	next_id: Arc<AtomicUsize>,
}
impl Default for IdProvider {
	fn default() -> Self {
		IdProvider {
			next_id: Arc::new(AtomicUsize::new(1)),
		}
	}
}

impl IdProvider {
	/// Returns next id for the subscription.
	pub fn next_id(&self) -> Id {
		self.next_id.fetch_add(1, atomic::Ordering::AcqRel) as u64
	}
}

/// Subscriptions manager.
///
/// Takes care of assigning unique subscription ids and
/// driving the sinks into completion.
#[derive(Clone)]
pub struct Subscriptions {
	next_id: IdProvider,
	active_subscriptions: Arc<Mutex<HashMap<Id, oneshot::Sender<()>>>>,
	executor: TaskExecutor,
}

impl Subscriptions {
	/// Creates new `Subscriptions` object.
	pub fn new(executor: TaskExecutor) -> Self {
		Subscriptions {
			next_id: Default::default(),
			active_subscriptions: Default::default(),
			executor,
		}
	}

	/// Borrows the internal task executor.
	///
	/// This can be used to spawn additional tasks on the underlying event loop.
	pub fn executor(&self) -> &TaskExecutor {
		&self.executor
	}

	/// Creates new subscription for given subscriber.
	///
	/// Second parameter is a function that converts Subscriber sink into a future.
	/// This future will be driven to completion by the underlying event loop
	/// or will be cancelled in case #cancel is invoked.
	pub fn add<T, E, G, R, F>(&self, subscriber: Subscriber<T, E>, into_future: G) -> SubscriptionId where
		G: FnOnce(Sink<T, E>) -> R,
		R: future::IntoFuture<Future=F, Item=(), Error=()>,
		F: future::Future<Item=(), Error=()> + Send + 'static,
	{
		let id = self.next_id.next_id();
		let subscription_id: SubscriptionId = id.into();
		if let Ok(sink) = subscriber.assign_id(subscription_id.clone()) {
			let (tx, rx) = oneshot::channel();
			let future = into_future(sink)
				.into_future()
				.select(rx.map_err(|e| warn!("Error timeing out: {:?}", e)))
				.then(|_| Ok(()));

			self.active_subscriptions.lock().insert(id, tx);
			if self.executor.execute(Box::new(future)).is_err() {
				error!("Failed to spawn RPC subscription task");
			}
		}

		subscription_id
	}

	/// Cancel subscription.
	///
	/// Returns true if subscription existed or false otherwise.
	pub fn cancel(&self, id: SubscriptionId) -> bool {
		if let SubscriptionId::Number(id) = id {
			if let Some(tx) = self.active_subscriptions.lock().remove(&id) {
				let _ = tx.send(());
				return true;
			}
		}
		false
	}
}
