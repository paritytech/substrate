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
//! api, the [`ApiExt`] trait, the [`CallApiAt`] trait and the [`ConstructRuntimeApi`] trait.

#![cfg_attr(not(feature = "std"), no_std)]

#[doc(hidden)]
#[cfg(feature = "std")]
pub use state_machine::{
	OverlayedChanges, StorageProof, Backend as StateBackend, ChangesTrieStorage,
};
#[doc(hidden)]
#[cfg(feature = "std")]
pub use primitives::NativeOrEncoded;
#[doc(hidden)]
#[cfg(feature = "std")]
pub use hash_db::Hasher;
#[doc(hidden)]
#[cfg(not(feature = "std"))]
pub use primitives::to_substrate_wasm_fn_return_value;
#[doc(hidden)]
pub use sr_primitives::{
	traits::{
		Block as BlockT, GetNodeBlockType, GetRuntimeBlockType, HasherFor, NumberFor,
		Header as HeaderT, Hash as HashT,
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

/// A type that records all accessed trie nodes and generates a proof out of it.
#[cfg(feature = "std")]
pub type ProofRecorder<B> = state_machine::ProofRecorder<
	<<<B as BlockT>::Header as HeaderT>::Hashing as HashT>::Hasher
>;

/// A type that is used as cache for the storage transactions.
#[cfg(feature = "std")]
pub type StorageTransactionCache<Block, Backend> =
	state_machine::StorageTransactionCache<
		<Backend as StateBackend<HasherFor<Block>>>::Transaction, HasherFor<Block>, NumberFor<Block>
	>;

#[cfg(feature = "std")]
pub type StorageChanges<SBackend, Block> =
	state_machine::StorageChanges<
		<SBackend as StateBackend<HasherFor<Block>>>::Transaction,
		HasherFor<Block>,
		NumberFor<Block>
	>;

/// Something that can be constructed to a runtime api.
#[cfg(feature = "std")]
pub trait ConstructRuntimeApi<Block: BlockT, C: CallApiAt<Block>> {
	/// The actual runtime api that will be constructed.
	type RuntimeApi: ApiExt<Block>;

	/// Construct an instance of the runtime api.
	fn construct_runtime_api<'a>(call: &'a C) -> ApiRef<'a, Self::RuntimeApi>;
}

/// Extends the runtime api traits with an associated error type. This trait is given as super
/// trait to every runtime api trait.
#[cfg(feature = "std")]
pub trait ApiErrorExt {
	/// Error type used by the runtime apis.
	type Error: std::fmt::Debug + From<String>;
}

/// Extends the runtime api implementation with some common functionality.
#[cfg(feature = "std")]
pub trait ApiExt<Block: BlockT>: ApiErrorExt {
	/// The state backend that is used to store the block states.
	type StateBackend: StateBackend<HasherFor<Block>>;

	/// The given closure will be called with api instance. Inside the closure any api call is
	/// allowed. After doing the api call, the closure is allowed to map the `Result` to a
	/// different `Result` type. This can be important, as the internal data structure that keeps
	/// track of modifications to the storage, discards changes when the `Result` is an `Err`.
	/// On `Ok`, the structure commits the changes to an internal buffer.
	fn map_api_result<F: FnOnce(&Self) -> result::Result<R, E>, R, E>(
		&self,
		map_call: F,
	) -> result::Result<R, E> where Self: Sized;

	/// Checks if the given api is implemented and versions match.
	fn has_api<A: RuntimeApiInfo + ?Sized>(
		&self,
		at: &BlockId<Block>,
	) -> Result<bool, Self::Error> where Self: Sized {
		self.runtime_version_at(at).map(|v| v.has_api_with(&A::ID, |v| v == A::VERSION))
	}

	/// Check if the given api is implemented and the version passes a predicate.
	fn has_api_with<A: RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
		&self,
		at: &BlockId<Block>,
		pred: P,
	) -> Result<bool, Self::Error> where Self: Sized {
		self.runtime_version_at(at).map(|v| v.has_api_with(&A::ID, pred))
	}

	/// Returns the runtime version at the given block id.
	fn runtime_version_at(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, Self::Error>;

	/// Start recording all accessed trie nodes for generating proofs.
	fn record_proof(&mut self);

	/// Extract the recorded proof.
	///
	/// This stops the proof recording.
	///
	/// If `record_proof` was not called before, this will return `None`.
	fn extract_proof(&mut self) -> Option<StorageProof>;

	/// Convert the api object into the storage changes that were done while executing runtime
	/// api functions.
	fn into_storage_changes<T: ChangesTrieStorage<HasherFor<Block>, NumberFor<Block>>>(
		self,
		backend: &Self::StateBackend,
		changes_trie_storage: Option<&T>,
		parent_hash: Block::Hash,
	) -> Result<StorageChanges<Self::StateBackend, Block>, String> where Self: Sized;
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

/// Parameters for [`CallApiAt::call_api_at`].
#[cfg(feature = "std")]
pub struct CallApiAtParams<'a, Block: BlockT, C, NC, Backend: StateBackend<HasherFor<Block>>> {
	/// A reference to something that implements the [`Core`] api.
	pub core_api: &'a C,
	/// The block id that determines the state that should be setup when calling the function.
	pub at: &'a BlockId<Block>,
	/// The name of the function that should be called.
	pub function: &'static str,
	/// An optional native call that calls the `function`. This is an optimization to call into a
	/// native runtime without requiring to encode/decode the parameters. The native runtime can
	/// still be called when this value is `None`, we then just fallback to encoding/decoding the
	/// parameters.
	pub native_call: Option<NC>,
	/// The encoded arguments of the function.
	pub arguments: Vec<u8>,
	/// The overlayed changes that are on top of the state.
	pub overlayed_changes: &'a RefCell<OverlayedChanges>,
	/// The cache for storage transactions.
	pub storage_transaction_cache: &'a RefCell<StorageTransactionCache<Block, Backend>>,
	/// Determines if the function requires that `initialize_block` should be called before calling
	/// the actual function.
	pub initialize_block: InitializeBlock<'a, Block>,
	/// The context this function is executed in.
	pub context: ExecutionContext,
	/// The optional proof recorder for recording storage accesses.
	pub recorder: &'a Option<ProofRecorder<Block>>,
}

/// Something that can call into the an api at a given block.
#[cfg(feature = "std")]
pub trait CallApiAt<Block: BlockT> {
	/// Error type used by the implementation.
	type Error: std::fmt::Debug + From<String>;

	/// The state backend that is used to store the block states.
	type StateBackend: StateBackend<HasherFor<Block>>;

	/// Calls the given api function with the given encoded arguments at the given block and returns
	/// the encoded result.
	fn call_api_at<
		'a,
		R: Encode + Decode + PartialEq,
		NC: FnOnce() -> result::Result<R, String> + UnwindSafe,
		C: Core<Block, Error = Self::Error>,
	>(
		&self,
		params: CallApiAtParams<'a, Block, C, NC, Self::StateBackend>,
	) -> Result<NativeOrEncoded<R>, Self::Error>;

	/// Returns the runtime version at the given block.
	fn runtime_version_at(&self, at: &BlockId<Block>) -> Result<RuntimeVersion, Self::Error>;
}

/// Auxiliary wrapper that holds an api instance and binds it to the given lifetime.
#[cfg(feature = "std")]
pub struct ApiRef<'a, T>(T, rstd::marker::PhantomData<&'a ()>);

#[cfg(feature = "std")]
impl<'a, T> ApiRef<'a, T> {
	/// Consume this type and call the given closure with the inner.
	///
	/// # Attention
	///
	/// The inner type should be consumed as well and not used outside of this ref. This is the
	/// reason why this function is `unsafe`.
	pub unsafe fn consume_inner<R>(self, consume: impl FnOnce(T) -> R) -> R {
		consume(self.0)
	}
}

#[cfg(feature = "std")]
impl<'a, T> From<T> for ApiRef<'a, T> {
	fn from(api: T) -> Self {
		ApiRef(api, Default::default())
	}
}

#[cfg(feature = "std")]
impl<'a, T> rstd::ops::Deref for ApiRef<'a, T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[cfg(feature = "std")]
impl<'a, T> rstd::ops::DerefMut for ApiRef<'a, T> {
	fn deref_mut(&mut self) -> &mut T {
		&mut self.0
	}
}

/// Something that provides a runtime api.
#[cfg(feature = "std")]
pub trait ProvideRuntimeApi<Block: BlockT> {
	/// The concrete type that provides the api.
	type Api: ApiExt<Block>;

	/// Returns the runtime api.
	/// The returned instance will keep track of modifications to the storage. Any successful
	/// call to an api function, will `commit` its changes to an internal buffer. Otherwise,
	/// the modifications will be `discarded`. The modifications will not be applied to the
	/// storage, even on a `commit`.
	fn runtime_api<'a>(&'a self) -> ApiRef<'a, Self::Api>;
}

/// Something that provides information about a runtime api.
#[cfg(feature = "std")]
pub trait RuntimeApiInfo {
	/// The identifier of the runtime api.
	const ID: [u8; 8];
	/// The version of the runtime api.
	const VERSION: u32;
}

/// Extracts the `Api::Error` for a type that provides a runtime api.
#[cfg(feature = "std")]
pub type ApiErrorFor<T, Block> = <<T as ProvideRuntimeApi<Block>>::Api as ApiErrorExt>::Error;

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
