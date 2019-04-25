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

//! Inherents Pool

use std::{fmt, mem, vec};
use parking_lot::Mutex;

/// Inherents Pool
///
/// The pool is responsible to collect inherents asynchronously generated
/// by some other parts of the code and make them ready for the next block production.
pub struct InherentsPool<T> {
	data: Mutex<Vec<T>>,
}

impl<T> Default for InherentsPool<T> {
	fn default() -> Self {
		InherentsPool {
			data: Default::default(),
		}
	}
}

impl<T: fmt::Debug> fmt::Debug for InherentsPool<T> {
	fn fmt(&self, fmt: &mut fmt::Formatter) -> fmt::Result {
		let mut builder = fmt.debug_struct("InherentsPool");
		if let Some(data) = self.data.try_lock() {
			builder.field("data", &*data);
		}
		builder.finish()
	}
}

impl<T> InherentsPool<T> {
	/// Add inherent extrinsic to the pool.
	///
	/// This inherent will be appended to the next produced block.
	pub fn add(&self, extrinsic: T) {
		self.data.lock().push(extrinsic);
	}

	/// Drain all currently queued inherents.
	pub fn drain(&self) -> Vec<T> {
		mem::replace(&mut *self.data.lock(), vec![])
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn should_drain_inherents_to_given_data() {
		let pool = InherentsPool::default();
		pool.add(5);
		pool.add(7);

		assert_eq!(pool.drain(), vec![5, 7]);
		assert_eq!(pool.drain(), vec![]);
	}
}
