// Copyright 2019 Parity Technologies (UK) Ltd.
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
