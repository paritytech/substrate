// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Externalities extensions storage.
//!
//! Externalities support to register a wide variety custom extensions. The [`Extensions`] provides
//! some convenience functionality to store and retrieve these extensions.
//!
//! It is required that each extension implements the [`Extension`] trait.

use sp_std::{
	collections::{btree_set::BTreeSet, btree_map::{BTreeMap, Entry}}, any::{Any, TypeId},
	ops::DerefMut, boxed::Box, mem,
};
use crate::Error;

/// Marker trait for types that should be registered as [`Externalities`](crate::Externalities) extension.
///
/// As extensions are stored as `Box<Any>`, this trait should give more confidence that the correct
/// type is registered and requested.
pub trait Extension: Send + Any {
	/// Return the extension as `&mut dyn Any`.
	///
	/// This is a trick to make the trait type castable into an `Any`.
	fn as_mut_any(&mut self) -> &mut dyn Any;
}

/// Macro for declaring an extension that usable with [`Extensions`].
///
/// The extension will be an unit wrapper struct that implements [`Extension`], `Deref` and
/// `DerefMut`. The wrapped type is given by the user.
///
/// # Example
/// ```
/// # use sp_externalities::decl_extension;
/// decl_extension! {
///     /// Some test extension
///     struct TestExt(String);
/// }
/// ```
#[macro_export]
macro_rules! decl_extension {
	(
		$( #[ $attr:meta ] )*
		$vis:vis struct $ext_name:ident ($inner:ty);
	) => {
		$( #[ $attr ] )*
		$vis struct $ext_name (pub $inner);

		impl $crate::Extension for $ext_name {
			fn as_mut_any(&mut self) -> &mut dyn std::any::Any {
				self
			}
		}

		impl std::ops::Deref for $ext_name {
			type Target = $inner;

			fn deref(&self) -> &Self::Target {
				&self.0
			}
		}

		impl std::ops::DerefMut for $ext_name {
			fn deref_mut(&mut self) -> &mut Self::Target {
				&mut self.0
			}
		}
	}
}

/// Something that provides access to the [`Extensions`] store.
///
/// This is a super trait of the [`Externalities`](crate::Externalities).
pub trait ExtensionStore {
	/// Tries to find a registered extension by the given `type_id` and returns it as a `&mut dyn Any`.
	///
	/// It is advised to use [`ExternalitiesExt::extension`](crate::ExternalitiesExt::extension)
	/// instead of this function to get type system support and automatic type downcasting.
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any>;

	/// Register extension `extension` with speciifed `type_id`.
	///
	/// It should return error if extension is already registered.
	fn register_extension_with_type_id(&mut self, type_id: TypeId, extension: Box<dyn Extension>) -> Result<(), Error>;

	/// Deregister extension with speicifed 'type_id' and drop it.
	///
	/// It should return error if extension is not registered.
	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), Error>;
}

/// The source from where an [`Extension`] is registered.
pub enum RegistrationSource {
	/// An extension is being registered from the runtime.
	Runtime,
	/// An extension is being registered from the client.
	Client,
}

impl RegistrationSource {
	/// Is the source the runtime?
	fn is_runtime(&self) -> bool {
		matches!(self, Self::Runtime)
	}
}

/// Stores extensions that should be made available through the externalities.
#[derive(Default)]
pub struct Extensions {
	extensions: BTreeMap<TypeId, Box<dyn Extension>>,
	/// Extensions that got registered from the runtime side.
	///
	/// If an extensions gets registered from the runtime side, it will be inserted here.
	///
	/// It will also be removed from the set when the extension is deregistered.
	runtime_registered_extensions: BTreeSet<TypeId>,
}

#[cfg(feature = "std")]
impl std::fmt::Debug for Extensions {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "Extensions: ({})", self.extensions.len())
	}
}

impl Extensions {
	/// Create new instance of `Self`.
	pub fn new() -> Self {
		Self::default()
	}

	/// Register the given extension.
	pub fn register<E: Extension>(
		&mut self,
		ext: E,
		registration_source: RegistrationSource,
	) {
		let type_id = ext.type_id();
		self.extensions.insert(type_id, Box::new(ext));

		if registration_source.is_runtime() {
			self.runtime_registered_extensions.insert(type_id);
		}
	}

	/// Register extension `ext`.
	pub fn register_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn Extension>,
		registration_source: RegistrationSource,
	) -> Result<(), Error> {
		match self.extensions.entry(type_id) {
			Entry::Vacant(vacant) => {
				vacant.insert(extension);
			},
			Entry::Occupied(_) => return Err(Error::ExtensionAlreadyRegistered),
		}

		if registration_source.is_runtime() {
			self.runtime_registered_extensions.insert(type_id);
		}

		Ok(())
	}

	/// Return a mutable reference to the requested extension.
	pub fn get_mut(&mut self, ext_type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(&ext_type_id).map(DerefMut::deref_mut).map(Extension::as_mut_any)
	}

	/// Deregister extension of type `E`.
	pub fn deregister(&mut self, type_id: TypeId) -> Option<Box<dyn Extension>> {
		let res = self.extensions.remove(&type_id);

		if res.is_some() {
			self.runtime_registered_extensions.remove(&type_id);
		}

		res
	}

	/// Remove all extensions that were registered from the runtime.
	pub fn remove_runtime_registered_extensions(&mut self) {
		let exts = mem::take(&mut self.runtime_registered_extensions);
		exts.into_iter().for_each(|ext| {
			self.extensions.remove(&ext);
		});
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	decl_extension! {
		struct DummyExt(u32);
	}
	decl_extension! {
		struct DummyExt2(u32);
	}

	#[test]
	fn register_and_retrieve_extension() {
		let mut exts = Extensions::new();
		exts.register(DummyExt(1), RegistrationSource::Client);
		exts.register(DummyExt2(2), RegistrationSource::Client);

		let ext = exts.get_mut(TypeId::of::<DummyExt>()).expect("Extension is registered");
		let ext_ty = ext.downcast_mut::<DummyExt>().expect("Downcasting works");

		assert_eq!(ext_ty.0, 1);
	}

	#[test]
	fn runtime_registered_extensions_is_maintained() {
		let mut exts = Extensions::new();
		exts.register(DummyExt(1), RegistrationSource::Runtime);
		assert!(exts.runtime_registered_extensions.contains(&TypeId::of::<DummyExt>()));
		exts.deregister(TypeId::of::<DummyExt>());
		assert!(!exts.runtime_registered_extensions.contains(&TypeId::of::<DummyExt>()));

		exts.register_with_type_id(
			TypeId::of::<DummyExt>(),
			Box::new(DummyExt(1)),
			RegistrationSource::Runtime,
		).unwrap();
		assert!(exts.runtime_registered_extensions.contains(&TypeId::of::<DummyExt>()));
		exts.deregister(TypeId::of::<DummyExt>());
		assert!(!exts.runtime_registered_extensions.contains(&TypeId::of::<DummyExt>()));
	}

	#[test]
	fn remove_runtime_registered_extensions_work() {
		let mut exts = Extensions::new();
		exts.register(DummyExt(1), RegistrationSource::Runtime);
		exts.register(DummyExt2(1), RegistrationSource::Client);

		exts.remove_runtime_registered_extensions();
		assert_eq!(1, exts.extensions.len());
		assert!(exts.runtime_registered_extensions.is_empty());
		assert!(exts.extensions.contains_key(&TypeId::of::<DummyExt2>()));
	}
}
