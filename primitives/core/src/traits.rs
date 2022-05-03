// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Shareable Substrate traits.

use std::{
	borrow::Cow,
	fmt::{Debug, Display},
	panic::UnwindSafe,
};

pub use sp_externalities::{Externalities, ExternalitiesExt};

/// Code execution engine.
pub trait CodeExecutor: Sized + Send + Sync + ReadRuntimeVersion + Clone + 'static {
	/// Externalities error type.
	type Error: Display + Debug + Send + Sync + 'static;

	/// Call a given method in the runtime. Returns a tuple of the result (either the output data
	/// or an execution error) together with a `bool`, which is true if native execution was used.
	fn call<
		R: codec::Codec + PartialEq,
		NC: FnOnce() -> Result<R, Box<dyn std::error::Error + Send + Sync>> + UnwindSafe,
	>(
		&self,
		ext: &mut dyn Externalities,
		runtime_code: &RuntimeCode,
		method: &str,
		data: &[u8],
		use_native: bool,
		native_call: Option<NC>,
	) -> (Result<crate::NativeOrEncoded<R>, Self::Error>, bool);
}

/// Something that can fetch the runtime `:code`.
pub trait FetchRuntimeCode {
	/// Fetch the runtime `:code`.
	///
	/// If the `:code` could not be found/not available, `None` should be returned.
	fn fetch_runtime_code(&self) -> Option<Cow<[u8]>>;
}

/// Wrapper to use a `u8` slice or `Vec` as [`FetchRuntimeCode`].
pub struct WrappedRuntimeCode<'a>(pub std::borrow::Cow<'a, [u8]>);

impl<'a> FetchRuntimeCode for WrappedRuntimeCode<'a> {
	fn fetch_runtime_code(&self) -> Option<Cow<[u8]>> {
		Some(self.0.as_ref().into())
	}
}

/// Type that implements [`FetchRuntimeCode`] and always returns `None`.
pub struct NoneFetchRuntimeCode;

impl FetchRuntimeCode for NoneFetchRuntimeCode {
	fn fetch_runtime_code(&self) -> Option<Cow<[u8]>> {
		None
	}
}

/// The Wasm code of a Substrate runtime.
#[derive(Clone)]
pub struct RuntimeCode<'a> {
	/// The code fetcher that can be used to lazily fetch the code.
	pub code_fetcher: &'a dyn FetchRuntimeCode,
	/// The optional heap pages this `code` should be executed with.
	///
	/// If `None` are given, the default value of the executor will be used.
	pub heap_pages: Option<u64>,
	/// The SCALE encoded hash of `code`.
	///
	/// The hashing algorithm isn't that important, as long as all runtime
	/// code instances use the same.
	pub hash: Vec<u8>,
}

impl<'a> PartialEq for RuntimeCode<'a> {
	fn eq(&self, other: &Self) -> bool {
		self.hash == other.hash
	}
}

impl<'a> RuntimeCode<'a> {
	/// Create an empty instance.
	///
	/// This is only useful for tests that don't want to execute any code.
	pub fn empty() -> Self {
		Self { code_fetcher: &NoneFetchRuntimeCode, hash: Vec::new(), heap_pages: None }
	}
}

impl<'a> FetchRuntimeCode for RuntimeCode<'a> {
	fn fetch_runtime_code(&self) -> Option<Cow<[u8]>> {
		self.code_fetcher.fetch_runtime_code()
	}
}

/// Could not find the `:code` in the externalities while initializing the [`RuntimeCode`].
#[derive(Debug)]
pub struct CodeNotFound;

impl std::fmt::Display for CodeNotFound {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
		write!(f, "the storage entry `:code` doesn't have any code")
	}
}

/// A trait that allows reading version information from the binary.
pub trait ReadRuntimeVersion: Send + Sync {
	/// Reads the runtime version information from the given wasm code.
	///
	/// The version information may be embedded into the wasm binary itself. If it is not present,
	/// then this function may fallback to the legacy way of reading the version.
	///
	/// The legacy mechanism involves instantiating the passed wasm runtime and calling
	/// `Core_version` on it. This is a very expensive operation.
	///
	/// `ext` is only needed in case the calling into runtime happens. Otherwise it is ignored.
	///
	/// Compressed wasm blobs are supported and will be decompressed if needed. If uncompression
	/// fails, the error is returned.
	///
	/// # Errors
	///
	/// If the version information present in binary, but is corrupted - returns an error.
	///
	/// Otherwise, if there is no version information present, and calling into the runtime takes
	/// place, then an error would be returned if `Core_version` is not provided.
	fn read_runtime_version(
		&self,
		wasm_code: &[u8],
		ext: &mut dyn Externalities,
	) -> Result<Vec<u8>, String>;
}

sp_externalities::decl_extension! {
	/// An extension that provides functionality to read version information from a given wasm blob.
	pub struct ReadRuntimeVersionExt(Box<dyn ReadRuntimeVersion>);
}

impl ReadRuntimeVersionExt {
	/// Creates a new instance of the extension given a version determinator instance.
	pub fn new<T: ReadRuntimeVersion + 'static>(inner: T) -> Self {
		Self(Box::new(inner))
	}
}

sp_externalities::decl_extension! {
	/// Task executor extension.
	pub struct TaskExecutorExt(Box<dyn SpawnNamed>);
}

impl TaskExecutorExt {
	/// New instance of task executor extension.
	pub fn new(spawn_handle: impl SpawnNamed + Send + 'static) -> Self {
		Self(Box::new(spawn_handle))
	}
}

/// Runtime spawn extension.
pub trait RuntimeSpawn: Send {
	/// Create new runtime instance and use dynamic dispatch to invoke with specified payload.
	///
	/// Returns handle of the spawned task.
	///
	/// Function pointers (`dispatcher_ref`, `func`) are WASM pointer types.
	fn spawn_call(&self, dispatcher_ref: u32, func: u32, payload: Vec<u8>) -> u64;

	/// Join the result of previously created runtime instance invocation.
	fn join(&self, handle: u64) -> Vec<u8>;
}

#[cfg(feature = "std")]
sp_externalities::decl_extension! {
	/// Extension that supports spawning extra runtime instances in externalities.
	pub struct RuntimeSpawnExt(Box<dyn RuntimeSpawn>);
}

/// Something that can spawn tasks (blocking and non-blocking) with an assigned name
/// and optional group.
#[dyn_clonable::clonable]
pub trait SpawnNamed: Clone + Send + Sync {
	/// Spawn the given blocking future.
	///
	/// The given `group` and `name` is used to identify the future in tracing.
	fn spawn_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	);
	/// Spawn the given non-blocking future.
	///
	/// The given `group` and `name` is used to identify the future in tracing.
	fn spawn(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	);
}

impl SpawnNamed for Box<dyn SpawnNamed> {
	fn spawn_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		(**self).spawn_blocking(name, group, future)
	}
	fn spawn(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		(**self).spawn(name, group, future)
	}
}

/// Something that can spawn essential tasks (blocking and non-blocking) with an assigned name
/// and optional group.
///
/// Essential tasks are special tasks that should take down the node when they end.
#[dyn_clonable::clonable]
pub trait SpawnEssentialNamed: Clone + Send + Sync {
	/// Spawn the given blocking future.
	///
	/// The given `group` and `name` is used to identify the future in tracing.
	fn spawn_essential_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	);
	/// Spawn the given non-blocking future.
	///
	/// The given `group` and `name` is used to identify the future in tracing.
	fn spawn_essential(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	);
}

impl SpawnEssentialNamed for Box<dyn SpawnEssentialNamed> {
	fn spawn_essential_blocking(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		(**self).spawn_essential_blocking(name, group, future)
	}

	fn spawn_essential(
		&self,
		name: &'static str,
		group: Option<&'static str>,
		future: futures::future::BoxFuture<'static, ()>,
	) {
		(**self).spawn_essential(name, group, future)
	}
}

/// Create random values of `Self` given a stream of entropy.
pub trait FromEntropy: Sized {
	/// Create a random value of `Self` given a stream of random bytes on `input`. May only fail if
	/// `input` has an error.
	fn from_entropy(input: &mut impl codec::Input) -> Result<Self, codec::Error>;
}

impl FromEntropy for bool {
	fn from_entropy(input: &mut impl codec::Input) -> Result<Self, codec::Error> {
		Ok(input.read_byte()? % 2 == 1)
	}
}

macro_rules! impl_from_entropy {
	($type:ty , $( $others:tt )*) => {
		impl_from_entropy!($type);
		impl_from_entropy!($( $others )*);
	};
	($type:ty) => {
		impl FromEntropy for $type {
			fn from_entropy(input: &mut impl codec::Input) -> Result<Self, codec::Error> {
				<Self as codec::Decode>::decode(input)
			}
		}
	}
}

macro_rules! impl_from_entropy_base {
	($type:ty , $( $others:tt )*) => {
		impl_from_entropy_base!($type);
		impl_from_entropy_base!($( $others )*);
	};
	($type:ty) => {
		impl_from_entropy!($type,
			[$type; 1], [$type; 2], [$type; 3], [$type; 4], [$type; 5], [$type; 6], [$type; 7], [$type; 8],
			[$type; 9], [$type; 10], [$type; 11], [$type; 12], [$type; 13], [$type; 14], [$type; 15], [$type; 16],
			[$type; 17], [$type; 18], [$type; 19], [$type; 20], [$type; 21], [$type; 22], [$type; 23], [$type; 24],
			[$type; 25], [$type; 26], [$type; 27], [$type; 28], [$type; 29], [$type; 30], [$type; 31], [$type; 32],
			[$type; 36], [$type; 40], [$type; 44], [$type; 48], [$type; 56], [$type; 64], [$type; 72], [$type; 80],
			[$type; 96], [$type; 112], [$type; 128], [$type; 160], [$type; 192], [$type; 224], [$type; 256]
		);
	}
}

impl_from_entropy_base!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128);
