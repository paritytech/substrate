// This file is part of Substrate.

// Copyright (C) 2020-2022 Parity Technologies (UK) Ltd.
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

use ::futures::channel::mpsc;

#[derive(Debug, Clone, Copy)]
pub struct Unbounded<T> {
	_pd: std::marker::PhantomData<T>,
}

impl<T> Channel for Unbounded<T> {
	type Tx = mpsc::UnboundedSender<T>;
	type Rx = mpsc::UnboundedReceiver<T>;

	fn create(&self) -> (Self::Tx, Self::Rx) {
		mpsc::unbounded()
	}
}
