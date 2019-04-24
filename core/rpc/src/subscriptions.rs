// Copyright 2017-2019 Parity Technologies (UK) Ltd
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.
use std::collections::HashMap;
use std::sync::{Arc, atomic::{self, AtomicUsize}};

use log::warn;
use jsonrpc_pubsub::{SubscriptionId, typed::{Sink, Subscriber}};
use parking_lot::Mutex;
use crate::rpc::futures::sync::oneshot;
use crate::rpc::futures::{Future, future};
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
	pub fn add<T, E, G, R, F>(&self, subscriber: Subscriber<T, E>, into_future: G) where
		G: FnOnce(Sink<T, E>) -> R,
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
