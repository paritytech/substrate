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

//! Substrate runtime api
//!
//! The Substrate runtime api is the crucial interface between the node and the runtime.
//! Every call that goes into the runtime is done with a runtime api. The runtime apis are not fixed.
//! Every Substrate user can define its own apis with
//! [`decl_runtime_apis`](macro.decl_runtime_apis.html) and implement them in
//! the runtime with [`impl_runtime_apis`](macro.impl_runtime_apis.html).
//!
//! Every Substrate runtime needs to implement the [`Core`] runtime api. This api provides the basic
//! functionality that every runtime needs to export.
//!
//! Besides the macros and the [`Core`] runtime api, this crates provides the [`Metadata`] runtime
//! api, the [`ApiExt`] trait, the [`CallRuntimeAt`] trait and the [`ConstructRuntimeApi`] trait.

#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
#[cfg(feature = "std")]
pub use state_machine::{OverlayedChanges, StorageProof};
#[doc(hidden)]
#[cfg(feature = "std")]
pub use primitives::NativeOrEncoded;
#[doc(hidden)]
#[cfg(not(feature = "std"))]
pub use primitives::to_substrate_wasm_fn_return_value;
#[doc(hidden)]
pub use sr_primitives::{
	traits::{
		Block as BlockT, GetNodeBlockType, GetRuntimeBlockType,
		Header as HeaderT, ApiRef, RuntimeApiInfo, Hash as HashT,
	},
	generic::BlockId, transaction_validity::TransactionValidity,
};
#[doc(hidden)]
pub use primitives::{offchain, ExecutionContext};
#[doc(hidden)]
pub use sr_version::{ApiId, RuntimeVersion, ApisVec, create_apis_vec};
#[doc(hidden)]
pub use rstd::{slice, mem};
#[cfg(feature = "std")]
use rstd::result;
#[doc(hidden)]
pub use codec::{Encode, Decode};
use primitives::OpaqueMetadata;
#[cfg(feature = "std")]
use std::{panic::UnwindSafe, cell::RefCell};

pub use sr_api_proc_macro::{decl_runtime_apis, impl_runtime_apis};

#[cfg(feature = "std")]
/// A type that records all accessed trie nodes and generates a proof out of it.
pub type ProofRecorder<B> = state_machine::ProofRecorder<
	<<<B as BlockT>::Header as HeaderT>::Hashing as HashT>::Hasher
>;

/// Something that can be constructed to a runtime api.
#[cfg(feature = "std")]
pub trait ConstructRuntimeApi<Block: BlockT, C: CallRuntimeAt<Block>> {
	/// The actual runtime api that will be constructed.
	type RuntimeApi;

	/// Construct an instance of the runtime api.
	fn construct_runtime_api<'a>(call: &'a C) -> ApiRef<'a, Self::RuntimeApi>;
}

/// An extension for the `RuntimeApi`.
#[cfg(feature = "std")]
pub trait ApiExt<Block: BlockT> {
	/// Error type used by the interface.
	type Error: std::fmt::Debug + From<String>;

	/// The given closure will be called with api instance. Inside the closure any api call is
	/// allowed. After doing the api call, the closure is allowed to map the `Result` to a
	/// different `Result` type. This can be important, as the internal data structure that keeps
	/// track of modifications to the storage, discards changes when the `Result` is an `Err`.
	/// On `Ok`, the structure commits the changes to an internal buffer.
	fn map_api_result<F: FnOnce(&Self) -> result::Result<R, E>, R, E>(
		&self,
		map_call: F
	) -> result::Result<R, E> where Self: Sized;

	/// Checks if the given api is implemented and versions match.
	fn has_api<A: RuntimeApiInfo + ?Sized>(
		&self,
		at: &BlockId<Block>
	) -> Result<bool, Self::Error> where Self: Sized {
		self.runtime_version_at(at).map(|v| v.has_api::<A>())
	}

	/// Check if the given api is implemented and the version passes a predicate.
	fn has_api_with<A: RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
		&self,
		at: &BlockId<Block>,
		pred: P,
	) -> Result<bool, Self::Error> where Self: Sized {
		self.runtime_version_at(at).map(|v| v.has_api_with::<A, _>(pred))
	}

	/// Returns the runtime version at the given block id.
	fn runtime_version_at(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, Self::Error>;

	/// Start recording all accessed trie nodes for generating proofs.
	fn record_proof(&mut self);

	/// Extract the recorded proof.
	/// This stops the proof recording.
	fn extract_proof(&mut self) -> Option<StorageProof>;
}

/// Before calling any runtime api function, the runtime need to be initialized
/// at the requested block. However, some functions like `execute_block` or
/// `initialize_block` itself don't require to have the runtime initialized
/// at the requested block.
///
/// `call_api_at` is instructed by this enum to do the initialization or to skip
/// it.
#[cfg(feature = "std")]
#[derive(Clone, Copy)]
pub enum InitializeBlock<'a, Block: BlockT> {
	/// Skip initializing the runtime for a given block.
	///
	/// This is used by functions who do the initialization by themselves or don't require it.
	Skip,
	/// Initialize the runtime for a given block.
	///
	/// If the stored `BlockId` is `Some(_)`, the runtime is currently initialized at this block.
	Do(&'a RefCell<Option<BlockId<Block>>>),
}

/// Something that can call into the runtime at a given block.
#[cfg(feature = "std")]
pub trait CallRuntimeAt<Block: BlockT> {
	/// Error type used by the interface.
	type Error: std::fmt::Debug + From<String>;

	/// Calls the given api function with the given encoded arguments at the given block and returns
	/// the encoded result.
	fn call_api_at<
		'a,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		C: Core<Block, Error = Self::Error>,
	>(
		&self,
		core_api: &C,
		at: &BlockId<Block>,
		function: &'static str,
		args: Vec<u8>,
		changes: &RefCell<OverlayedChanges>,
		initialize_block: InitializeBlock<'a, Block>,
		native_call: Option<NC>,
		context: ExecutionContext,
		recorder: &Option<ProofRecorder<Block>>,
	) -> Result<NativeOrEncoded<R>, Self::Error>;

	/// Returns the runtime version at the given block.
	fn runtime_version_at(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, Self::Error>;
}

/// Extracts the `Api::Error` for a type that provides a runtime api.
#[cfg(feature = "std")]
pub type ApiErrorFor<T, Block> = <
	<T as sr_primitives::traits::ProvideRuntimeApi>::Api as ApiExt<Block>
>::Error;

decl_runtime_apis! {
	/// The `Core` runtime api that every Substrate runtime needs to implement.
	#[core_trait]
	#[api_version(2)]
	pub trait Core {
		/// Returns the version of the runtime.
		fn version() -> RuntimeVersion;
		/// Execute the given block.
		#[skip_initialize_block]
		fn execute_block(block: Block);
		/// Initialize a block with the given header.
		#[renamed("initialise_block", 2)]
		#[skip_initialize_block]
		#[initialize_block]
		fn initialize_block(header: &<Block as BlockT>::Header);
	}

	/// The `Metadata` api trait that returns metadata for the runtime.
	pub trait Metadata {
		/// Returns the metadata of a runtime.
		fn metadata() -> OpaqueMetadata;
	}
}
