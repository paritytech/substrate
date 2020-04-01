// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! This is part of the Substrate runtime.

use sp_core::{ed25519, sr25519, crypto::Pair, traits::CloneableSpawn};
use std::sync::{Arc, atomic::{AtomicBool, Ordering as AtomicOrdering}};
use futures::{future::FutureExt, task::FutureObj, channel::oneshot};

#[derive(Debug, Clone)]
struct Ed25519BatchItem {
	signature: ed25519::Signature,
	pub_key: ed25519::Public,
	message: Vec<u8>,
}

#[derive(Debug, Clone)]
struct Sr25519BatchItem {
	signature: sr25519::Signature,
	pub_key: sr25519::Public,
	message: Vec<u8>,
}

/// Batch verifier.
///
/// Used to parallel-verify signatures for runtime host. Provide task executor and
/// just push (`push_ed25519`, `push_sr25519`) as many signature as you need. At the end,
/// call `verify_and_clear to get a result. After that, batch verifier is ready for the
/// next batching job.
pub struct BatchVerifier {
	scheduler: Box<dyn CloneableSpawn>,
	sr25519_items: Vec<Sr25519BatchItem>,
	invalid: Arc<AtomicBool>,
	pending_tasks: Vec<oneshot::Receiver<()>>,
}

impl BatchVerifier {
	pub fn new(scheduler: Box<dyn CloneableSpawn>) -> Self {
		BatchVerifier {
			scheduler,
			sr25519_items: Default::default(),
			invalid: Arc::new(false.into()),
			pending_tasks: vec![],
		}
	}

	fn spawn_verification_task(&mut self, f: impl FnOnce() -> bool + Send + 'static) {
		// there is already invalid transaction encountered
		if self.invalid.load(AtomicOrdering::Relaxed) { return; }

		let invalid_clone = self.invalid.clone();
		let (sender, receiver) = oneshot::channel();
		self.pending_tasks.push(receiver);

		self.scheduler.spawn_obj(FutureObj::new(async move {
			if !f() {
				invalid_clone.store(true, AtomicOrdering::Relaxed);
			}
			if let Err(_) = sender.send(()) {
				// sanity
				log::warn!("Verification halted while result was pendign");
				invalid_clone.store(true, AtomicOrdering::Relaxed);
			}
		}.boxed())).expect("Scheduler should not fail");
	}

	/// Push ed25519 signature to verify.
	pub fn push_ed25519(
		&mut self,
		signature: ed25519::Signature,
		pub_key: ed25519::Public,
		message: Vec<u8>,
	) {
		if self.invalid.load(AtomicOrdering::Relaxed) { return; } // there is already invalid transaction encountered

		self.spawn_verification_task(move || ed25519::Pair::verify(&signature, &message, &pub_key));
	}

	/// Push sr25519 signature to verify.
	pub fn push_sr25519(
		&mut self,
		signature: sr25519::Signature,
		pub_key: sr25519::Public,
		message: Vec<u8>,
	) {
		self.sr25519_items.push(Sr25519BatchItem { signature, pub_key, message });
	}

	/// Verify all previously pushed signatures since last call and return
	/// aggregated result.
	pub fn verify_and_clear(&mut self) -> bool {
		use parking_lot::{Mutex, Condvar};

		let pending = std::mem::replace(&mut self.pending_tasks, vec![]);

		if pending.len() > 0 {
			let pair = Arc::new((Mutex::new(()), Condvar::new()));
			let pair_clone = pair.clone();
			self.scheduler.spawn_obj(FutureObj::new(async move {
				futures::future::join_all(pending).await;
				pair_clone.1.notify_one();
			}.boxed())).expect("Scheduler should not fail");

			let (mtx, cond_var) = &*pair;
			let mut mtx = mtx.lock();
			cond_var.wait(&mut mtx);
		}

		let messages = self.sr25519_items.iter().map(|item| &item.message[..]).collect();
		let signatures = self.sr25519_items.iter().map(|item| &item.signature).collect();
		let pub_keys = self.sr25519_items.iter().map(|item| &item.pub_key).collect();

		if !sr25519::verify_batch(messages, signatures, pub_keys) {
			self.sr25519_items.clear();

			return false;
		}

		self.sr25519_items.clear();

		if self.invalid.load(AtomicOrdering::Relaxed) {
			self.invalid.store(false, AtomicOrdering::Relaxed);
			return false;
		}

		debug_assert_eq!(self.sr25519_items.len(), 0);

		true
	}
}
