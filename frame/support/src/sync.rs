// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Types used to sync access to shared data. All of these types rely on the assumption
//! that no data parallelism exists within the runtime.

use sp_std::{
	cell::{Cell, RefCell},
	ops::{Deref, DerefMut},
};

/// A [`Sync`] version of [`Cell`]. Safe to use within the runtime.
pub struct RuntimeCell<T>(Cell<T>);

impl<T> RuntimeCell<T> {
	/// See [`Cell::new`]
	pub const fn new(value: T) -> Self {
		Self(Cell::new(value))
	}
}

unsafe impl<T> Sync for RuntimeCell<T> {}

impl<T> Deref for RuntimeCell<T> {
	type Target = Cell<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T> DerefMut for RuntimeCell<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}

/// A [`Sync`] version of [`RefCell`]. Safe to use within the runtime.
pub struct RuntimeRefCell<T>(RefCell<T>);

impl<T> RuntimeRefCell<T> {
	/// See [`RefCell::new`]
	pub const fn new(value: T) -> Self {
		Self(RefCell::new(value))
	}
}

unsafe impl<T> Sync for RuntimeRefCell<T> {}

impl<T> Deref for RuntimeRefCell<T> {
	type Target = RefCell<T>;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

impl<T> DerefMut for RuntimeRefCell<T> {
	fn deref_mut(&mut self) -> &mut Self::Target {
		&mut self.0
	}
}
