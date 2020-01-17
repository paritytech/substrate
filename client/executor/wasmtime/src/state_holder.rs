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

use crate::function_executor::{HostState, HostContext};
use std::cell::{self, RefCell};
use std::rc::Rc;

#[derive(Clone)]
pub struct StateHolder {
	// This is `Some` only during a call.
	state: Rc<RefCell<Option<HostState>>>,
}

impl StateHolder {
	pub fn empty() -> StateHolder {
		StateHolder {
			state: Rc::new(RefCell::new(None)),
		}
	}

	pub fn init_state<R, F>(&self, state: &mut HostState, f: F) -> R
	where
		F: FnOnce() -> R,
	{
		// We need an `Option` here since Rust will doesn't allow to assign a value for the first
		// time from within a closure.
		let mut ret: Option<R> = None;

		take_mut::take(state, |state| {
			*self.state.borrow_mut() = Some(state);

			ret = Some(f());

			let state = self
				.state
				.borrow_mut()
				.take()
				.expect("cannot be None since was just assigned; qed");

			state
		});

		ret.expect("cannot be None since was just in the closure above; qed")
	}

	pub fn with_context<R, F>(&self, f: F) -> R
	where
		F: FnOnce(HostContext) -> R,
	{
		let state = self.state.borrow();
		match *state {
			Some(ref state) => f(state.materialize()),
			None => panic!(),
		}
	}
}
