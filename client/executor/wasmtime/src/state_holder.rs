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

use crate::host::{HostContext, HostState};

scoped_tls::scoped_thread_local!(static HOST_STATE: HostState);

/// A common place to store a reference to the `HostState`.
///
/// This structure is passed into each host function handler and retained in the implementation of
/// `WasmRuntime`. Whenever a call into a runtime method is initiated, the host state is populated
/// with the state for that runtime method call.
///
/// During the execution of the runtime method call, wasm can call imported host functions. When
/// that happens the host function handler gets a `HostContext` (obtainable through having a
/// `HostState` reference).
#[derive(Clone)]
pub struct StateHolder;

impl StateHolder {
	/// Create a placeholder `StateHolder`.
	pub fn new() -> StateHolder {
		StateHolder
	}

	/// Provide `HostState` for the runtime method call and execute the given function `f`.
	///
	/// During the execution of the provided function `with_context` will be callable.
	pub fn with_initialized_state<R, F>(&self, s: &HostState, f: F) -> R
	where
		F: FnOnce() -> R,
	{
		HOST_STATE.set(s, || {
			f()
		})
	}

	/// Create a `HostContext` from the contained `HostState` and execute the given function `f`.
	///
	/// This function is only callable within closure passed to `init_state`. Otherwise, the passed
	/// context will be `None`.
	pub fn with_context<R, F>(&self, f: F) -> R
	where
		F: FnOnce(Option<HostContext>) -> R,
	{
		if !HOST_STATE.is_set() {
			return f(None)
		}
		HOST_STATE.with(|state| f(Some(state.materialize())))
	}
}
