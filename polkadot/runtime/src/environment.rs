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

//! Environment API: Allows certain information to be accessed throughout the runtime.

use rstd::boxed::Box;
use rstd::cell::RefCell;
use rstd::rc::Rc;

use polkadot_primitives::{BlockNumber, Digest, Hash};

#[derive(Default)]
/// The information that can be accessed globally.
pub struct Environment {
	/// The current block number.
	pub block_number: BlockNumber,
	/// The current block's parent hash.
	pub parent_hash: Hash,
	/// The current block digest.
	pub digest: Digest,
	/// The current transaction index
	pub transaction_index: u64,
}

/// Do something with the environment and return its value. Keep the function short.
pub fn with_env<T, F: FnOnce(&mut Environment) -> T>(f: F) -> T {
	let e = env();
	let mut eb = e.borrow_mut();
	f(&mut *eb)
}

#[cfg(target_arch = "wasm32")]
fn env() -> Rc<RefCell<Environment>> {
	// Initialize it to a null value
	static mut SINGLETON: *const Rc<RefCell<Environment>> = 0 as *const Rc<RefCell<Environment>>;

	unsafe {
		if SINGLETON == 0 as *const Rc<RefCell<Environment>> {
			// Make it
			let singleton: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Default::default()));

			// Put it in the heap so it can outlive this call
			SINGLETON = Box::into_raw(Box::new(singleton)) as *const _;
		}

		// Now we give out a copy of the data that is safe to use concurrently.
		(*SINGLETON).clone()
	}
}

#[cfg(not(target_arch = "wasm32"))]
fn env() -> Rc<RefCell<Environment>> {
	// Initialize it to a null value
	thread_local!{
		static SINGLETON: RefCell<*const Rc<RefCell<Environment>>> = RefCell::new(0 as *const Rc<RefCell<Environment>>);
	}

	SINGLETON.with(|s| unsafe {
		if *s.borrow() == 0 as *const Rc<RefCell<Environment>> {
			// Make it
			let singleton: Rc<RefCell<Environment>> = Rc::new(RefCell::new(Default::default()));

			// Put it in the heap so it can outlive this call
			*s.borrow_mut() = Box::into_raw(Box::new(singleton)) as *const _;
		}

		// Now we give out a copy of the data that is safe to use concurrently.
		(**s.borrow()).clone()
	})
}
