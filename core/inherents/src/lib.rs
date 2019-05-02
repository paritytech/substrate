// Copyright 2019 Parity Technologies (UK) Ltd.
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

//! Provides types and traits for creating and checking inherents.
//!
//! Each inherent is added to a produced block. Each runtime decides on which inherents its
//! want to attach to its blocks. All data that is required for the runtime to create the inherents
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

use parity_codec as codec;
use codec::{Encode, Decode};

use rstd::{collections::btree_map::{BTreeMap, IntoIter, Entry}, vec::Vec};

#[cfg(feature = "std")]
use parking_lot::RwLock;

#[cfg(feature = "std")]
use std::{sync::Arc, format};

#[cfg(feature = "std")]
pub mod pool;

pub use runtime_primitives::RuntimeString;

/// An identifier for an inherent.
pub type InherentIdentifier = [u8; 8];

/// Inherent data to include in a block.
#[derive(Clone, Default)]
pub struct InherentData {
	/// All inherent data encoded with parity-codec and an identifier.
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
	/// Returns `Ok(())` if the data could be inserted an no data for an inherent with the same
	/// identifier existed, otherwise an error is returned.
	///
	/// Inherent identifiers need to be unique, otherwise decoding of these values will not work!
	pub fn put_data<I: codec::Encode>(
		&mut self,
		identifier: InherentIdentifier,
		inherent: &I,
	) -> Result<(), RuntimeString> {
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
	) -> Result<Option<I>, RuntimeString> {
		match self.data.get(identifier) {
			Some(inherent) =>
				I::decode(&mut &inherent[..])
					.ok_or_else(|| {
						"Could not decode requested inherent type!".into()
					})
					.map(Some),
			None => Ok(None)
		}
	}
}

impl codec::Encode for InherentData {
	fn encode(&self) -> Vec<u8> {
		let keys = self.data.keys().collect::<Vec<_>>();
		let values = self.data.values().collect::<Vec<_>>();

		let mut encoded = keys.encode();
		encoded.extend(values.encode());
		encoded
	}
}

impl codec::Decode for InherentData {
	fn decode<I: codec::Input>(value: &mut I) -> Option<Self> {
		Vec::<InherentIdentifier>::decode(value)
			.and_then(|i| Vec::<Vec<u8>>::decode(value).map(|v| (i, v)))
			.and_then(|(i, v)| {
				if i.len() == v.len() {
					Some(Self {
						data: i.into_iter().zip(v.into_iter()).collect()
					})
				} else {
					None
				}
			})
	}
}

/// The result of checking inherents.
///
/// It either returns okay for all checks, stores all occurred errors or just one fatal error.
///
/// When a fatal error occurres, all other errors are removed and the implementation needs to
/// abbort checking inherents.
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
	) -> Result<(), RuntimeString> {
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
	) -> Result<Option<E>, RuntimeString> {
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

/// All `InherentData` providers.
#[cfg(feature = "std")]
#[derive(Clone, Default)]
pub struct InherentDataProviders {
	providers: Arc<RwLock<Vec<Box<dyn ProvideInherentData + Send + Sync>>>>,
}

#[cfg(feature = "std")]
impl InherentDataProviders {
	/// Create a new instance.
	pub fn new() -> Self {
		Self::default()
	}

	/// Register an `InherentData` provider.
	///
	/// The registration order is preserved and this order will also be used when creating the
	/// inherent data.
	///
	/// # Result
	///
	/// Will return an error, if a provider with the same identifier already exists.
	pub fn register_provider<P: ProvideInherentData + Send + Sync +'static>(
		&self,
		provider: P,
	) -> Result<(), RuntimeString> {
		if self.has_provider(&provider.inherent_identifier()) {
			Err(
				format!(
					"Inherent data provider with identifier {:?} already exists!",
					&provider.inherent_identifier()
				).into()
			)
		} else {
			provider.on_register(self)?;
			self.providers.write().push(Box::new(provider));
			Ok(())
		}
	}

	/// Returns if a provider for the given identifier exists.
	pub fn has_provider(&self, identifier: &InherentIdentifier) -> bool {
		self.providers.read().iter().any(|p| p.inherent_identifier() == identifier)
	}

	/// Create inherent data.
	pub fn create_inherent_data(&self) -> Result<InherentData, RuntimeString> {
		let mut data = InherentData::new();
		self.providers.read().iter().try_for_each(|p| {
			p.provide_inherent_data(&mut data)
				.map_err(|e| format!("Error for `{:?}`: {:?}", p.inherent_identifier(), e))
		})?;
		Ok(data)
	}

	/// Converts a given encoded error into a `String`.
	///
	/// Useful if the implementation encouters an error for an identifier it does not know.
	pub fn error_to_string(&self, identifier: &InherentIdentifier, error: &[u8]) -> String {
		let res = self.providers.read().iter().filter_map(|p|
			if p.inherent_identifier() == identifier {
				Some(
					p.error_to_string(error)
						.unwrap_or_else(|| error_to_string_fallback(identifier))
				)
			} else {
				None
			}
		).next();

		match res {
			Some(res) => res,
			None => format!(
				"Error while checking inherent of type \"{}\", but this inherent type is unknown.",
				String::from_utf8_lossy(identifier)
			)
		}
	}
}

/// Something that provides inherent data.
#[cfg(feature = "std")]
pub trait ProvideInherentData {
	/// Is called when this inherent data provider is registered at the given
	/// `InherentDataProviders`.
	fn on_register(&self, _: &InherentDataProviders) -> Result<(), RuntimeString> {
		Ok(())
	}

	/// The identifier of the inherent for that data will be provided.
	fn inherent_identifier(&self) -> &'static InherentIdentifier;

	/// Provide inherent data that should be included in a block.
	///
	/// The data should be stored in the given `InherentData` structure.
	fn provide_inherent_data(&self, inherent_data: &mut InherentData) -> Result<(), RuntimeString>;

	/// Convert the given encoded error to a string.
	///
	/// If the given error could not be decoded, `None` should be returned.
	fn error_to_string(&self, error: &[u8]) -> Option<String>;
}

/// A fallback function, if the decoding of an error fails.
#[cfg(feature = "std")]
fn error_to_string_fallback(identifier: &InherentIdentifier) -> String {
	format!(
		"Error while checking inherent of type \"{}\", but error could not be decoded.",
		String::from_utf8_lossy(identifier)
	)
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

/// A module that provides an inherent and may also verifies it.
pub trait ProvideInherent {
	/// The call type of the module.
	type Call;
	/// The error returned by `check_inherent`.
	type Error: codec::Encode + IsFatalError;
	/// The inherent identifier used by this inherent.
	const INHERENT_IDENTIFIER: self::InherentIdentifier;

	/// Create an inherent out of the given `InherentData`.
	fn create_inherent(data: &InherentData) -> Option<Self::Call>;

	/// Check the given inherent if it is valid.
	/// Checking the inherent is optional and can be omitted.
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
	struct TestInherentDataProvider {
		registered: Arc<RwLock<bool>>,
	}

	impl TestInherentDataProvider {
		fn new() -> Self {
			let inst = Self {
				registered: Default::default(),
			};

			// just make sure
			assert!(!inst.is_registered());

			inst
		}

		fn is_registered(&self) -> bool {
			*self.registered.read()
		}
	}

	const ERROR_TO_STRING: &str = "Found error!";

	impl ProvideInherentData for TestInherentDataProvider {
		fn on_register(&self, _: &InherentDataProviders) -> Result<(), RuntimeString> {
			*self.registered.write() = true;
			Ok(())
		}

		fn inherent_identifier(&self) -> &'static InherentIdentifier {
			&TEST_INHERENT_0
		}

		fn provide_inherent_data(&self, data: &mut InherentData) -> Result<(), RuntimeString> {
			data.put_data(TEST_INHERENT_0, &42)
		}

		fn error_to_string(&self, _: &[u8]) -> Option<String> {
			Some(ERROR_TO_STRING.into())
		}
	}

	#[test]
	fn registering_inherent_provider() {
		let provider = TestInherentDataProvider::new();
		let providers = InherentDataProviders::new();

		providers.register_provider(provider.clone()).unwrap();
		assert!(provider.is_registered());
		assert!(providers.has_provider(provider.inherent_identifier()));

		// Second time should fail
		assert!(providers.register_provider(provider.clone()).is_err());
	}

	#[test]
	fn create_inherent_data_from_all_providers() {
		let provider = TestInherentDataProvider::new();
		let providers = InherentDataProviders::new();

		providers.register_provider(provider.clone()).unwrap();
		assert!(provider.is_registered());

		let inherent_data = providers.create_inherent_data().unwrap();

		assert_eq!(
			inherent_data.get_data::<u32>(provider.inherent_identifier()).unwrap().unwrap(),
			42u32
		);
	}

	#[test]
	fn encoded_error_to_string() {
		let provider = TestInherentDataProvider::new();
		let providers = InherentDataProviders::new();

		providers.register_provider(provider.clone()).unwrap();
		assert!(provider.is_registered());

		assert_eq!(
			&providers.error_to_string(&TEST_INHERENT_0, &[1, 2]), ERROR_TO_STRING
		);

		assert!(
			providers
				.error_to_string(&TEST_INHERENT_1, &[1, 2])
				.contains("inherent type is unknown")
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
