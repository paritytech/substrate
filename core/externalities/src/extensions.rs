// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Externalities extensions storage.
//!
//! Externalities support to register a wide variety custom extensions. The [`Extensions`] provides
//! some convenience functionality to store and retrieve these extensions.
//!
//! It is required that each extension implements the [`Extension`] trait.

use std::{collections::HashMap, any::{Any, TypeId}, ops::DerefMut};

/// Marker trait for types that should be registered as `Externalities` extension.
///
/// As extensions are stored as `Box<Any>`, this trait should give more confidence that the correct
/// type is registered and requested.
pub trait Extension: Sized {}

/// Stores extensions that should be made available through the externalities.
#[derive(Default)]
pub struct Extensions {
	extensions: HashMap<TypeId, Box<dyn Any>>,
}

impl Extensions {
	/// Create new instance of `Self`.
	pub fn new() -> Self {
		Self::default()
	}

	/// Register the given extension.
	pub fn register<E: Any + Extension>(&mut self, ext: E) {
		self.extensions.insert(ext.type_id(), Box::new(ext));
	}

	/// Return a mutable reference to the requested extension.
	pub fn get_mut(&mut self, ext_type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(&ext_type_id).map(DerefMut::deref_mut)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	struct DummyExt(u32);
	impl Extension for DummyExt {}

	struct DummyExt2(u32);
	impl Extension for DummyExt2 {}

	#[test]
	fn register_and_retrieve_extension() {
		let mut exts = Extensions::new();
		exts.register(DummyExt(1));
		exts.register(DummyExt2(2));

		let ext = exts.get_mut(TypeId::of::<DummyExt>()).expect("Extension is registered");
		let ext_ty = ext.downcast_mut::<DummyExt>().expect("Downcasting works");

		assert_eq!(ext_ty.0, 1);
	}
}
