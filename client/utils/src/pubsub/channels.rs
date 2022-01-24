// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

use super::*;

use crate::mpsc;

#[derive(Debug, Copy)]
pub struct TracingUnbounded<Item> {
	key: &'static str,
	_pd: std::marker::PhantomData<Item>,
}

impl<Item> TracingUnbounded<Item> {
	pub fn new(key: &'static str) -> Self {
		Self { key, _pd: Default::default() }
	}
}

impl<Item> Unpin for TracingUnbounded<Item> {}

impl<Item> Clone for TracingUnbounded<Item> {
	fn clone(&self) -> Self {
		Self { key: self.key, _pd: Default::default() }
	}
}

impl<Item> Channel for TracingUnbounded<Item> {
	type Tx = mpsc::TracingUnboundedSender<Item>;
	type Rx = mpsc::TracingUnboundedReceiver<Item>;
	type Item = Item;

	fn create(&self) -> (Self::Tx, Self::Rx) {
		mpsc::tracing_unbounded(self.key)
	}

	fn send(&self, tx: &mut Self::Tx, item: Self::Item) {
		let _ = tx.unbounded_send(item);
	}
}
