// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Provides types and traits for creating and checking inherents.
//!
//! Each inherent is added to a produced block. Each runtime decides on which inherents it
//! wants to attach to its blocks. All data that is required for the runtime to create the inherents
//! is stored in the `InherentData`. This `InherentData` is constructed by the node and given to
//! the runtime.
//!
//! Types that provide data for inherents, should implement `InherentDataProvider` and need to be
//! registered at `InherentDataProviders`.
//!
//! In the runtime, modules need to implement `ProvideInherent` when they can create and/or check
//! inherents. By implementing `ProvideInherent`, a module is not enforced to create an inherent.
//! A module can also just check given inherents. For using a module as inherent provider, it needs
//! to be registered by the `construct_runtime!` macro. The macro documentation gives more
//! information on how that is done.

#![cfg_attr(not(feature = "std"), no_std)]
#![warn(missing_docs)]

use codec::{Encode, Decode};

use sp_std::{collections::btree_map::{BTreeMap, IntoIter, Entry}, vec::Vec};

#[cfg(feature = "std")]
use sp_runtime::traits::Block as BlockT;

/// An error that can occur within the inherent data system.
#[cfg(feature = "std")]
#[derive(Debug, Encode, Decode, thiserror::Error)]
#[error("Inherents: {0}")]
pub struct Error(String);

#[cfg(feature = "std")]
impl<T: Into<String>> From<T> for Error {
	fn from(data: T) -> Error {
		Self(data.into())
	}
}

#[cfg(feature = "std")]
impl Error {
	/// Convert this error into a `String`.
	pub fn into_string(self) -> String {
		self.0
	}
}

/// An error that can occur within the inherent data system.
#[derive(Encode, sp_core::RuntimeDebug)]
#[cfg(not(feature = "std"))]
pub struct Error(&'static str);

#[cfg(not(feature = "std"))]
impl From<&'static str> for Error {
	fn from(data: &'static str) -> Error {
		Self(data)
	}
}

/// An identifier for an inherent.
pub type InherentIdentifier = [u8; 8];

/// Inherent data to include in a block.
#[derive(Clone, Default, Encode, Decode)]
pub struct InherentData {
	/// All inherent data encoded with parity-scale-codec and an identifier.
	data: BTreeMap<InherentIdentifier, Vec<u8>>
}

impl InherentData {
	/// Create a new instance.
	pub fn new() -> Self {
		Self::default()
	}

	/// Put data for an inherent into the internal storage.
	///
	/// # Return
	///
	/// Returns `Ok(())` if the data could be inserted and no data for an inherent with the same
	/// identifier existed, otherwise an error is returned.
	///
	/// Inherent identifiers need to be unique, otherwise decoding of these values will not work!
	pub fn put_data<I: codec::Encode>(
		&mut self,
		identifier: InherentIdentifier,
		inherent: &I,
	) -> Result<(), Error> {
		match self.data.entry(identifier) {
			Entry::Vacant(entry) => {
				entry.insert(inherent.encode());
				Ok(())
			},
			Entry::Occupied(_) => {
				Err("Inherent with same identifier already exists!".into())
			}
		}
	}

	/// Replace the data for an inherent.
	///
	/// If it does not exist, the data is just inserted.
	pub fn replace_data<I: codec::Encode>(
		&mut self,
		identifier: InherentIdentifier,
		inherent: &I,
	) {
		self.data.insert(identifier, inherent.encode());
	}

	/// Returns the data for the requested inherent.
	///
	/// # Return
	///
	/// - `Ok(Some(I))` if the data could be found and deserialized.
	/// - `Ok(None)` if the data could not be found.
	/// - `Err(_)` if the data could be found, but deserialization did not work.
	pub fn get_data<I: codec::Decode>(
		&self,
		identifier: &InherentIdentifier,
	) -> Result<Option<I>, Error> {
		match self.data.get(identifier) {
			Some(inherent) =>
				I::decode(&mut &inherent[..])
					.map_err(|_| {
						"Could not decode requested inherent type!".into()
					})
					.map(Some),
			None => Ok(None)
		}
	}

	/// Get the number of inherents in this instance
	pub fn len(&self) -> usize {
		self.data.len()
	}
}

/// The result of checking inherents.
///
/// It either returns okay for all checks, stores all occurred errors or just one fatal error.
///
/// When a fatal error occurs, all other errors are removed and the implementation needs to
/// abort checking inherents.
#[derive(Encode, Decode, Clone)]
pub struct CheckInherentsResult {
	/// Did the check succeed?
	okay: bool,
	/// Did we encounter a fatal error?
	fatal_error: bool,
	/// We use the `InherentData` to store our errors.
	errors: InherentData,
}

impl Default for CheckInherentsResult {
	fn default() -> Self {
		Self {
			okay: true,
			errors: InherentData::new(),
			fatal_error: false,
		}
	}
}

impl CheckInherentsResult {
	/// Create a new instance.
	pub fn new() -> Self {
		Self::default()
	}

	/// Put an error into the result.
	///
	/// This makes this result resolve to `ok() == false`.
	///
	/// # Parameters
	///
	/// - identifier - The identifier of the inherent that generated the error.
	/// - error - The error that will be encoded.
	pub fn put_error<E: codec::Encode + IsFatalError>(
		&mut self,
		identifier: InherentIdentifier,
		error: &E,
	) -> Result<(), Error> {
		// Don't accept any other error
		if self.fatal_error {
			return Err("No other errors are accepted after an hard error!".into())
		}

		if error.is_fatal_error() {
			// remove the other errors.
			self.errors.data.clear();
		}

		self.errors.put_data(identifier, error)?;

		self.okay = false;
		self.fatal_error = error.is_fatal_error();
		Ok(())
	}

	/// Get an error out of the result.
	///
	/// # Return
	///
	/// - `Ok(Some(I))` if the error could be found and deserialized.
	/// - `Ok(None)` if the error could not be found.
	/// - `Err(_)` if the error could be found, but deserialization did not work.
	pub fn get_error<E: codec::Decode>(
		&self,
		identifier: &InherentIdentifier,
	) -> Result<Option<E>, Error> {
		self.errors.get_data(identifier)
	}

	/// Convert into an iterator over all contained errors.
	pub fn into_errors(self) -> IntoIter<InherentIdentifier, Vec<u8>> {
		self.errors.data.into_iter()
	}

	/// Is this result ok?
	pub fn ok(&self) -> bool {
		self.okay
	}

	/// Is this a fatal error?
	pub fn fatal_error(&self) -> bool {
		self.fatal_error
	}
}

#[cfg(feature = "std")]
impl PartialEq for CheckInherentsResult {
	fn eq(&self, other: &Self) -> bool {
		self.fatal_error == other.fatal_error &&
		self.okay == other.okay &&
		self.errors.data == other.errors.data
	}
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
pub trait CreateInherentDataProviders<Block: BlockT, ExtraArgs> {
	/// The inherent data providers that will be created.
	type InherentDataProviders: InherentDataProvider;

	/// Create the inherent data providers at the given `parent` block using the given `extra_args`.
	async fn create_inherent_data_providers(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<Self::InherentDataProviders, Box<dyn std::error::Error + Send + Sync>>;
}

#[cfg(feature = "std")]
#[async_trait::async_trait]
impl<F, Block, IDP, ExtraArgs, Fut> CreateInherentDataProviders<Block, ExtraArgs> for F
where
	Block: BlockT,
	F: Fn(Block::Hash, ExtraArgs) -> Fut + Sync + Send,
	Fut: std::future::Future<Output = Result<IDP, Box<dyn std::error::Error + Send + Sync>>> + Send + 'static,
	IDP: InherentDataProvider + 'static,
	ExtraArgs: Send + 'static,
{
	type InherentDataProviders = IDP;

	async fn create_inherent_data_providers(
		&self,
		parent: Block::Hash,
		extra_args: ExtraArgs,
	) -> Result<Self::InherentDataProviders, Box<dyn std::error::Error + Send + Sync>> {
		(*self)(parent, extra_args).await
	}
}


/// Result of [`InherentDataProvider::try_handle_error`].
#[cfg(feature = "std")]
pub type TryHandleErrorResult =
	Option<
		std::pin::Pin<
			Box<
				dyn std::future::Future<Output = Result<(), Box<dyn std::error::Error + Send + Sync>>> + Send
			>
		>
	>;

/// Something that provides inherent data.
#[cfg(feature = "std")]
pub trait InherentDataProvider: Send + Sync {
	/// Convenience function for creating [`InherentData`].
	///
	/// Basically maps around [`Self::provide_inherent_data`].
	fn create_inherent_data(&self) -> Result<InherentData, Error> {
		let mut inherent_data = InherentData::new();
		self.provide_inherent_data(&mut inherent_data)?;
		Ok(inherent_data)
	}

	/// Provide inherent data that should be included in a block.
	///
	/// The data should be stored in the given `InherentData` structure.
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error>;

	/// Convert the given encoded error to a string.
	///
	/// If the given error could not be decoded, `None` should be returned.
	fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> TryHandleErrorResult;
}

#[cfg(feature = "std")]
#[impl_trait_for_tuples::impl_for_tuples(10)]
impl InherentDataProvider for Tuple {
	for_tuples!( where #( Tuple: Send + Sync )* );
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), Error> {
		for_tuples!( #( Tuple.provide_inherent_data(inherent_data)?; )* );
		Ok(())
	}

	fn try_handle_error(
		&self,
		identifier: &InherentIdentifier,
		error: &[u8],
	) -> TryHandleErrorResult {
		for_tuples!( #(
			if let Some(e) = Tuple.try_handle_error(identifier, error) { return Some(e) }
		)* );

		None
	}
}

/// Did we encounter a fatal error while checking an inherent?
///
/// A fatal error is everything that fails while checking an inherent error, e.g. the inherent
/// was not found, could not be decoded etc.
/// Then there are cases where you not want the inherent check to fail, but report that there is an
/// action required. For example a timestamp of a block is in the future, the timestamp is still
/// correct, but it is required to verify the block at a later time again and then the inherent
/// check will succeed.
pub trait IsFatalError {
	/// Is this a fatal error?
	fn is_fatal_error(&self) -> bool;
}

/// Auxiliary to make any given error resolve to `is_fatal_error() == true`.
#[derive(Encode)]
pub struct MakeFatalError<E: codec::Encode>(E);

impl<E: codec::Encode> From<E> for MakeFatalError<E> {
	fn from(err: E) -> Self {
		MakeFatalError(err)
	}
}

impl<E: codec::Encode> IsFatalError for MakeFatalError<E> {
	fn is_fatal_error(&self) -> bool {
		true
	}
}

/// A pallet that provides or verifies an inherent extrinsic.
///
/// The pallet may provide the inherent, verify an inherent, or both provide and verify.
pub trait ProvideInherent {
	/// The call type of the pallet.
	type Call;
	/// The error returned by `check_inherent`.
	type Error: codec::Encode + IsFatalError;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: self::InherentIdentifier;

	/// Create an inherent out of the given `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call>;

	/// Determines whether this inherent is required in this block.
	///
	/// - `Ok(None)` indicates that this inherent is not required in this block. The default
	/// implementation returns this.
	///
	/// - `Ok(Some(e))` indicates that this inherent is required in this block. The
	/// `impl_outer_inherent!`, will call this function from its `check_extrinsics`.
	/// If the inherent is not present, it will return `e`.
	///
	/// - `Err(_)` indicates that this function failed and further operations should be aborted.
	///
	/// CAUTION: This check has a bug when used in pallets that also provide unsigned transactions.
	/// See <https://github.com/paritytech/substrate/issues/6243> for details.
	fn is_inherent_required(_: &InherentData) -> Result<Option<Self::Error>, Self::Error> { Ok(None) }

	/// Check whether the given inherent is valid. Checking the inherent is optional and can be
	/// omitted by using the default implementation.
	///
	/// When checking an inherent, the first parameter represents the inherent that is actually
	/// included in the block by its author. Whereas the second parameter represents the inherent
	/// data that the verifying node calculates.
	fn check_inherent(_: &Self::Call, _: &InherentData) -> Result<(), Self::Error> {
		Ok(())
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use codec::{Encode, Decode};

	const TEST_INHERENT_0: InherentIdentifier = *b"testinh0";
	const TEST_INHERENT_1: InherentIdentifier = *b"testinh1";

	#[derive(Encode)]
	struct NoFatalError<E: codec::Encode>(E);
	impl<E: codec::Encode> IsFatalError for NoFatalError<E> {
		fn is_fatal_error(&self) -> bool {
			false
		}
	}

	#[test]
	fn inherent_data_encodes_and_decodes() {
		let inherent_0 = vec![1, 2, 3];
		let inherent_1: u32 = 7;

		let mut data = InherentData::new();
		data.put_data(TEST_INHERENT_0, &inherent_0).unwrap();
		data.put_data(TEST_INHERENT_1, &inherent_1).unwrap();

		let encoded = data.encode();

		let decoded = InherentData::decode(&mut &encoded[..]).unwrap();

		assert_eq!(decoded.get_data::<Vec<u32>>(&TEST_INHERENT_0).unwrap().unwrap(), inherent_0);
		assert_eq!(decoded.get_data::<u32>(&TEST_INHERENT_1).unwrap().unwrap(), inherent_1);
	}

	#[test]
	fn adding_same_inherent_returns_an_error() {
		let mut data = InherentData::new();
		data.put_data(TEST_INHERENT_0, &8).unwrap();
		assert!(data.put_data(TEST_INHERENT_0, &10).is_err());
	}

	#[derive(Clone)]
	struct TestInherentDataProvider;

	const ERROR_TO_STRING: &str = "Found error!";

	impl InherentDataProvider for TestInherentDataProvider {
		fn provide_inherent_data(&self, data: &mut InherentData) -> Result<(), Error> {
			data.put_data(TEST_INHERENT_0, &42)
		}

		fn try_handle_error(
			&self,
			_: &InherentIdentifier,
			_: &[u8],
		) -> TryHandleErrorResult {
			Some(Box::pin(async move { Err(Box::from(ERROR_TO_STRING)) }))
		}
	}

	#[test]
	fn create_inherent_data() {
		let provider = TestInherentDataProvider;

		let inherent_data = provider.create_inherent_data().unwrap();

		assert_eq!(
			inherent_data.get_data::<u32>(&TEST_INHERENT_0).unwrap().unwrap(),
			42u32,
		);
	}

	#[test]
	fn check_inherents_result_encodes_and_decodes() {
		let mut result = CheckInherentsResult::new();
		assert!(result.ok());

		result.put_error(TEST_INHERENT_0, &NoFatalError(2u32)).unwrap();
		assert!(!result.ok());
		assert!(!result.fatal_error());

		let encoded = result.encode();

		let decoded = CheckInherentsResult::decode(&mut &encoded[..]).unwrap();

		assert_eq!(decoded.get_error::<u32>(&TEST_INHERENT_0).unwrap().unwrap(), 2);
		assert!(!decoded.ok());
		assert!(!decoded.fatal_error());
	}

	#[test]
	fn check_inherents_result_removes_other_errors_on_fatal_error() {
		let mut result = CheckInherentsResult::new();
		assert!(result.ok());

		result.put_error(TEST_INHERENT_0, &NoFatalError(2u32)).unwrap();
		assert!(!result.ok());
		assert!(!result.fatal_error());

		result.put_error(TEST_INHERENT_1, &MakeFatalError(4u32)).unwrap();
		assert!(!result.ok());
		assert!(result.fatal_error());

		assert!(result.put_error(TEST_INHERENT_0, &NoFatalError(5u32)).is_err());

		result.into_errors().for_each(|(i, e)| match i {
			TEST_INHERENT_1 => assert_eq!(u32::decode(&mut &e[..]).unwrap(), 4),
			_ => panic!("There should be no other error!"),
		});
	}
}
