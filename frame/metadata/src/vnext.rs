// This file is part of Substrate.

// Copyright (C) 2018-2020 Parity Technologies (UK) Ltd.
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

//! Decodable variant of the RuntimeMetadata.
//!
//! This really doesn't belong here, but is necessary for the moment. In the future
//! it should be removed entirely to an external module for shimming on to the
//! codec-encoded metadata.

#![cfg_attr(not(feature = "std"), no_std)]

#[cfg(feature = "std")]
use codec::{Decode, Input};
use codec::Encode;
use sp_core::RuntimeDebug;
use sp_std::{
	vec::Vec,
	fmt::Debug,
};

use scale_info::{
	form::{
		PortableForm,
		Form,
		FormString,
		MetaForm,
	},
	meta_type,
	IntoPortable,
	Registry,
	PortableRegistry,
	TypeInfo,
};

pub type RuntimeMetadataLastVersion<T> = RuntimeMetadataV12<T>;

/// Metadata prefixed by a u32 for reserved usage
#[derive(Eq, Encode, PartialEq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct RuntimeMetadataPrefixed<S = &'static str>
where
	S: FormString,
{
	pub prefix: u32,
	pub types: PortableRegistry<S>,
	pub metadata: RuntimeMetadata<PortableForm<S>>,
}

impl From<RuntimeMetadataLastVersion<MetaForm>> for RuntimeMetadataPrefixed {
	fn from(metadata: RuntimeMetadataLastVersion<MetaForm>) -> RuntimeMetadataPrefixed {
		let mut registry = Registry::new();
		let metadata = metadata.into_portable(&mut registry);
		RuntimeMetadataPrefixed {
			prefix: super::META_RESERVED,
			types: registry.into(),
			metadata: RuntimeMetadata::V12(metadata),
		}
	}
}

impl From<RuntimeMetadataPrefixed> for sp_core::OpaqueMetadata {
	fn from(metadata: RuntimeMetadataPrefixed) -> Self {
		sp_core::OpaqueMetadata::new(metadata.encode())
	}
}

/// The metadata of a runtime.
/// The version ID encoded/decoded through
/// the enum nature of `RuntimeMetadata`.
#[derive(Eq, Encode, PartialEq, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub enum RuntimeMetadata<T: Form = MetaForm> {
	/// Version 12 for runtime metadata.
	V12(RuntimeMetadataV12<T>),
}

/// The metadata of a runtime.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct RuntimeMetadataV12<T: Form = MetaForm> {
	/// Metadata of all the modules.
	pub modules: Vec<ModuleMetadata<T>>,
	// /// Metadata of the extrinsic.
	// pub extrinsic: ExtrinsicMetadata<F>,
}

impl IntoPortable for RuntimeMetadataV12 {
	type Output = RuntimeMetadataV12<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		RuntimeMetadataV12 {
			modules: registry.map_into_portable(self.modules),
			// extrinsic: self.extrinsic.into_portable(registry),
		}
	}
}

/// Metadata of the extrinsic used by the runtime.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct ExtrinsicMetadata<T: Form = MetaForm> {
	/// Extrinsic version.
	pub version: u8,
	/// The signed extensions in the order they appear in the extrinsic.
	pub signed_extensions: Vec<T::Type>,
}

impl IntoPortable for ExtrinsicMetadata {
	type Output = ExtrinsicMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		ExtrinsicMetadata {
			version: self.version,
			signed_extensions: registry.register_types(self.signed_extensions),
		}
	}
}

/// All metadata about an runtime module.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct ModuleMetadata<T: Form = MetaForm> {
	pub name: T::String,
	// pub storage: Option<DecodeDifferent<FnEncode<StorageMetadata>, StorageMetadata>>,
	pub calls: Option<Vec<FunctionMetadata<T>>>,
	pub event: Option<Vec<EventMetadata<T>>>,
	// pub constants: DFnA<ModuleConstantMetadata>,
	// pub errors: DFnA<ErrorMetadata>,
}

impl IntoPortable for ModuleMetadata {
	type Output = ModuleMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		ModuleMetadata {
			name: self.name.into_portable(registry),
			calls: self.calls.map(|calls| registry.map_into_portable(calls)),
			event: self.event.map(|event| registry.map_into_portable(event)),
		}
	}
}

/// All the metadata about a function.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct FunctionMetadata<T: Form = MetaForm> {
	pub name: T::String,
	pub arguments: Vec<FunctionArgumentMetadata<T>>,
	pub documentation: Vec<T::String>,
}

impl IntoPortable for FunctionMetadata {
	type Output = FunctionMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		FunctionMetadata {
			name: self.name.into_portable(registry),
			arguments: registry.map_into_portable(self.arguments),
			documentation: registry.map_into_portable(self.documentation),
		}
	}
}

/// All the metadata about a function argument.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct FunctionArgumentMetadata<T: Form = MetaForm> {
	pub name: T::String,
	pub ty: T::Type,
	pub is_compact: bool,
}

impl IntoPortable for FunctionArgumentMetadata {
	type Output = FunctionArgumentMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		FunctionArgumentMetadata {
			name: self.name.into_portable(registry),
			ty: registry.register_type(&self.ty),
			is_compact: self.is_compact,
		}
	}
}

/// All the metadata about an outer event.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct OuterEventMetadata<T: Form = MetaForm> {
	pub name: T::String,
	pub events: Vec<ModuleEventMetadata<T>>,
}

impl IntoPortable for OuterEventMetadata {
	type Output = OuterEventMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		OuterEventMetadata {
			name: self.name.into_portable(registry),
			events: registry.map_into_portable(self.events),
		}
	}
}

/// Metadata about a module event.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct ModuleEventMetadata<T: Form = MetaForm> {
	pub name: T::String,
	pub events: Vec<EventMetadata<T>>,
}

impl IntoPortable for ModuleEventMetadata {
	type Output = ModuleEventMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		ModuleEventMetadata {
			name: self.name.into_portable(registry),
			events: registry.map_into_portable(self.events),
		}
	}
}

/// All the metadata about an event.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct EventMetadata<T: Form = MetaForm> {
	pub name: T::String,
	pub arguments: Vec<TypeSpec<T>>,
	pub documentation: Vec<T::String>,
}

impl IntoPortable for EventMetadata {
	type Output = EventMetadata<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		EventMetadata {
			name: self.name.into_portable(registry),
			arguments: registry.map_into_portable(self.arguments),
			documentation: registry.map_into_portable(self.documentation),
		}
	}
}

/// A type specification.
///
/// This contains the actual type as well as an optional compile-time
/// known displayed representation of the type. This is useful for cases
/// where the type is used through a type alias in order to provide
/// information about the alias name.
///
/// # Examples
///
/// Consider the following Rust function:
/// ```no_compile
/// fn is_sorted(input: &[i32], pred: Predicate) -> bool;
/// ```
/// In this above example `input` would have no displayable name,
/// `pred`'s display name is `Predicate` and the display name of
/// the return type is simply `bool`. Note that `Predicate` could
/// simply be a type alias to `fn(i32, i32) -> Ordering`.
#[derive(Clone, PartialEq, Eq, Encode, RuntimeDebug)]
#[cfg_attr(feature = "std", derive(Decode))]
pub struct TypeSpec<T: Form = MetaForm> {
	/// The actual type.
	ty: T::Type,
	/// The compile-time known displayed representation of the type.
	name: T::String,
}

impl IntoPortable for TypeSpec {
	type Output = TypeSpec<PortableForm>;

	fn into_portable(self, registry: &mut Registry) -> Self::Output {
		TypeSpec {
			ty: registry.register_type(&self.ty),
			name: self.name.into_portable(registry),
		}
	}
}

impl TypeSpec {
	/// Creates a new type specification without a display name.
	pub fn new<T>(name: &'static str) -> Self
		where
			T: TypeInfo + 'static,
	{
		Self {
			ty: meta_type::<T>(),
			name,
		}
	}
}
