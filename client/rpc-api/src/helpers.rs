// Copyright 2018-2020 Parity Technologies (UK) Ltd.
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

use jsonrpc_core::futures::prelude::*;
use futures::{channel::oneshot, compat::Compat};

/// Wraps around `oneshot::Receiver` and adjusts the error type to produce an internal error if the
/// sender gets dropped.
pub struct Receiver<T>(pub Compat<oneshot::Receiver<T>>);

impl<T> Future for Receiver<T> {
	type Item = T;
	type Error = jsonrpc_core::Error;

	fn poll(&mut self) -> Poll<Self::Item, Self::Error> {
		self.0.poll().map_err(|_| jsonrpc_core::Error::internal_error())
	}
}
