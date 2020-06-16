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

//! Strongly typed interface for SignedExtensions
//!

use sp_runtime::traits::{StaticLookup, SignedExtension};
use sp_runtime::generic::Era;

/// AccountIndex type for Runtime
pub type IndexFor<R> = <R as crate::Trait>::Index;
/// Call type for Runtime
pub type CallFor<R> = <R as crate::Trait>::Call;
/// Address type for runtime.
pub type AddressFor<R> = <<R as crate::Trait>::Lookup as StaticLookup>::Source;
/// Hash for runtime.
pub type HashFor<R> = <R as crate::Trait>::Hash;
/// AccountId type for runtime.
pub type AccountIdFor<R> = <R as crate::Trait>::AccountId;

/// Strongly typed interface for the `SignedExtensions` that should be included in extrinsics
/// for them to valid for your runtime.
pub trait SignedExtensionProvider: crate::Trait {
	/// Concrete SignedExtension type.
	type Extra: SignedExtension;

	/// Concrete type for params used to construct the `SignedExtension`-Data
	type Builder: ExtrasParamsBuilder<Self>;

	/// Retrieve an instance of the builder.
	fn extras_params_builder() -> Self::Builder;

	/// Construct extras and optionally additional_signed data for inclusion in extrinsics.
	fn construct_extras(input: <Self::Builder as ExtrasParamsBuilder<Self>>::ExtrasParams) ->
		SignedExtensionData<Self::Extra>;
}


/// Extras that should be included in extrinsics,
/// additional data is provided for call sites that don't have access to storage.
pub struct SignedExtensionData<S: SignedExtension> {
	/// Signed extras
	pub extra: S,
	/// Additional data for the signed extras.
	pub additional: Option<S::AdditionalSigned>,
}

/// Builder for `ExtrasParams`, used by runtimes to define data required for constructing signed extras
pub trait ExtrasParamsBuilder<T: crate::Trait> {
	/// Concrete type passed to `construct_extras`.
	type ExtrasParams;

	/// Sets the tip
	fn set_tip(self, tip: u128) -> Self;
	
	/// Sets the block hash for the start of the era this transaction is valid for.
	/// this is an additional signed data and is therefore **optional**
	/// only provide it you know `construct_extras` will be called outside of an externalities environment.
	fn set_starting_era_hash(self, hash: T::Hash) -> Self;
	
	/// Sets the genesis hash
	/// this is an additional signed data and is therefore **optional**
	/// only provide it you know `construct_extras` will be called outside of an externalities environment.
	fn set_genesis_hash(self, hash: T::Hash) -> Self;
	
	/// build the extras params
	fn build(self, nonce: T::Index, era: Era) -> Self::ExtrasParams;
}
