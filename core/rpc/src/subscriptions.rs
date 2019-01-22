// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use jsonrpc_macros::pubsub;
use jsonrpc_pubsub::SubscriptionId;
use parking_lot::Mutex;
use rpc::futures::sync::oneshot;
use rpc::futures::{Future, future};
use tokio::runtime::TaskExecutor;

type Id = u64;

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
#[derive(Debug, Clone)]
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

	/// Creates new subscription for given subscriber.
	///
	/// Second parameter is a function that converts Subscriber sink into a future.
	/// This future will be driven to completion bu underlying event loop
	/// or will be cancelled in case #cancel is invoked.
	pub fn add<T, E, G, R, F>(&self, subscriber: pubsub::Subscriber<T, E>, into_future: G) where
		G: FnOnce(pubsub::Sink<T, E>) -> R,
		R: future::IntoFuture<Future=F, Item=(), Error=()>,
		F: future::Future<Item=(), Error=()> + Send + 'static,
	{
		let id = self.next_id.next_id();
		if let Ok(sink) = subscriber.assign_id(id.into()) {
			let (tx, rx) = oneshot::channel();
			let future = into_future(sink)
				.into_future()
				.select(rx.map_err(|e| warn!("Error timeing out: {:?}", e)))
				.then(|_| Ok(()));

			self.active_subscriptions.lock().insert(id, tx);
			self.executor.spawn(future);
		}
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
