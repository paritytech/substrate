// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Testing utils used by the RPC tests.

use std::{future::Future, sync::Arc};

/// A task executor that can be used for running RPC tests.
///
/// Warning: the tokio runtime must be initialized before calling this.
#[derive(Clone)]
pub struct TokioTestExecutor(tokio::runtime::Handle);

impl TokioTestExecutor {
	/// Create a new instance of `Self`.
	pub fn new() -> Self {
		Self(tokio::runtime::Handle::current())
	}
}

impl Default for TokioTestExecutor {
	fn default() -> Self {
		Self::new()
	}
}

impl sp_core::traits::SpawnNamed for TokioTestExecutor {
	fn spawn_blocking(
		&self,
		_name: &'static str,
		_group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		let handle = self.0.clone();
		self.0.spawn_blocking(move || {
			handle.block_on(future);
		});
	}
	fn spawn(
		&self,
		_name: &'static str,
		_group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		self.0.spawn(future);
	}
}

/// Executor for testing.
pub fn test_executor() -> Arc<TokioTestExecutor> {
	Arc::new(TokioTestExecutor::default())
}

/// Wrap a future in a timeout a little more concisely
pub fn timeout_secs<I, F: Future<Output = I>>(s: u64, f: F) -> tokio::time::Timeout<F> {
	tokio::time::timeout(std::time::Duration::from_secs(s), f)
}
