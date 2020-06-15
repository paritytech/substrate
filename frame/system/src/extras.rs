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

///
/// Strongly typed interface for the `SignedExtensions` that should be included in extrinsics
/// for them to valid for your runtime.
///
/// ```rust
/// use runtime::{Runtime, SignedExtra};
/// use frame_system::extras::IndexFor;
///
/// #[derive(Default)]
/// struct ExtraParams {
///		
/// }
///
/// impl SignedExtensionProvider for Runtime {
///     type Extra = SignedExtra;
///
///		type Params = ExtraParams;
///	
///		fn extension_params() -> Self::Params {
///			Default::default()
/// 	}
///		
///     fn construct_extras(params: ExtraParams) -> Result<SignedExtensionData<Self::Extra>, &'static str> {
///         // take the biggest period possible.
///         let period = BlockHashCount::get()
///             .checked_next_power_of_two()
///             .map(|c| c / 2)
///             .unwrap_or(2) as u64;
///         let current_block = System::block_number()
///             .saturated_into::<u64>()
///             // The `System::block_number` is initialized with `n+1`,
///             // so the actual block number is `n`.
///             .saturating_sub(1);
///
///         (
///             frame_system::CheckSpecVersion::new(),
///             frame_system::CheckTxVersion::new(),
///             frame_system::CheckGenesis::new(),
///             frame_system::CheckEra::from(generic::Era::mortal(period, current_block)),
///             frame_system::CheckNonce::from(index),
///             frame_system::CheckWeight::new(),
///         )
///     }
/// }
///
/// ```
///
pub trait SignedExtensionProvider: crate::Trait {
    /// Concrete SignedExtension type.
	type Extra: SignedExtension;
	/// Concrete type for params used to construct the `SignedExtension`-Data
	type Params: SystemExtraParams<Self>;

	/// retrieve an instance of the input object.
	fn extension_params() -> Self::Params;

    /// construct extras and optionally additional_signed data for inclusion in extrinsics.
    fn construct_extras(input: Self::Params) -> Result<SignedExtensionData<Self::Extra>, &'static str>;
}

/// extras that should be included in extrinsics,
/// additional data is provided for call sites that don't have access to storage.
pub struct SignedExtensionData<S: SignedExtension> {
	/// signed extras
	pub extra: S,
	/// additional data for the signed extras.
	pub additional: Option<S::AdditionalSigned>,
}

/// used internally by substrate to set extras for inclusion in 
/// `SignedExtensionProvider`
pub trait SystemExtraParams<T: crate::Trait> {
	/// sets the nonce
	fn set_nonce(&mut self, index: T::Index);
	/// sets the nonce
	fn set_era(&mut self, era: Era);
	/// sets the block hash for the start of the era this transaction is valid for.
	fn set_starting_era_hash(&mut self, hash: T::Hash);
	/// set the genesis hash
	fn set_genesis_hash(&mut self, hash: T::Hash);
}
