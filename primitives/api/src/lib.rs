// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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
//!
//! On a meta level this implies, the client calls the generated API from the client perspective.

#![cfg_attr(not(feature = "std"), no_std)]

// Make doc tests happy
extern crate self as sp_api;

#[doc(hidden)]
#[cfg(feature = "std")]
pub use sp_state_machine::{
	OverlayedChanges, StorageProof, Backend as StateBackend, ChangesTrieState, InMemoryBackend,
};
#[doc(hidden)]
#[cfg(feature = "std")]
pub use sp_core::NativeOrEncoded;
#[doc(hidden)]
#[cfg(feature = "std")]
pub use hash_db::Hasher;
#[cfg(feature = "std")]
pub use sp_core::offchain::storage::OffchainOverlayedChanges;
#[doc(hidden)]
#[cfg(not(feature = "std"))]
pub use sp_core::to_substrate_wasm_fn_return_value;
#[doc(hidden)]
pub use sp_runtime::{
	traits::{
		Block as BlockT, GetNodeBlockType, GetRuntimeBlockType, HashFor, NumberFor,
		Header as HeaderT, Hash as HashT,
	},
	generic::BlockId, transaction_validity::TransactionValidity, RuntimeString, TransactionOutcome,
};
#[doc(hidden)]
pub use sp_core::{offchain, ExecutionContext};
#[doc(hidden)]
pub use sp_version::{ApiId, RuntimeVersion, ApisVec, create_apis_vec};
#[doc(hidden)]
pub use sp_std::{slice, mem};
#[cfg(feature = "std")]
use sp_std::result;
#[doc(hidden)]
pub use codec::{Encode, Decode, DecodeLimit};
use sp_core::OpaqueMetadata;
#[cfg(feature = "std")]
use std::{panic::UnwindSafe, cell::RefCell};

/// Maximum nesting level for extrinsics.
pub const MAX_EXTRINSIC_DEPTH: u32 = 256;

/// Declares given traits as runtime apis.
///
/// The macro will create two declarations, one for using on the client side and one for using
/// on the runtime side. The declaration for the runtime side is hidden in its own module.
/// The client side declaration gets two extra parameters per function,
/// `&self` and `at: &BlockId<Block>`. The runtime side declaration will match the given trait
/// declaration. Besides one exception, the macro adds an extra generic parameter `Block: BlockT`
/// to the client side and the runtime side. This generic parameter is usable by the user.
///
/// For implementing these macros you should use the
/// [`impl_runtime_apis!`](macro.impl_runtime_apis.html) macro.
///
/// # Example
///
/// ```rust
/// sp_api::decl_runtime_apis! {
///     /// Declare the api trait.
///     pub trait Balance {
///         /// Get the balance.
///         fn get_balance() -> u64;
///         /// Set the balance.
///         fn set_balance(val: u64);
///     }
///
///     /// You can declare multiple api traits in one macro call.
///     /// In one module you can call the macro at maximum one time.
///     pub trait BlockBuilder {
///         /// The macro adds an explicit `Block: BlockT` generic parameter for you.
///         /// You can use this generic parameter as you would defined it manually.
///         fn build_block() -> Block;
///     }
/// }
///
/// # fn main() {}
/// ```
///
/// # Runtime api trait versioning
///
/// To support versioning of the traits, the macro supports the attribute `#[api_version(1)]`.
/// The attribute supports any `u32` as version. By default, each trait is at version `1`, if no
/// version is provided. We also support changing the signature of a method. This signature
/// change is highlighted with the `#[changed_in(2)]` attribute above a method. A method that is
/// tagged with this attribute is callable by the name `METHOD_before_version_VERSION`. This
/// method will only support calling into wasm, trying to call into native will fail (change the
/// spec version!). Such a method also does not need to be implemented in the runtime. It is
/// required that there exist the "default" of the method without the `#[changed_in(_)]` attribute,
/// this method will be used to call the current default implementation.
///
/// ```rust
/// sp_api::decl_runtime_apis! {
///     /// Declare the api trait.
///     #[api_version(2)]
///     pub trait Balance {
///         /// Get the balance.
///         fn get_balance() -> u64;
///         /// Set balance.
///         fn set_balance(val: u64);
///         /// Set balance, old version.
///         ///
///         /// Is callable by `set_balance_before_version_2`.
///         #[changed_in(2)]
///         fn set_balance(val: u16);
///         /// In version 2, we added this new function.
///         fn increase_balance(val: u64);
///     }
/// }
///
/// # fn main() {}
/// ```
///
/// To check if a given runtime implements a runtime api trait, the `RuntimeVersion` has the
/// function `has_api<A>()`. Also the `ApiExt` provides a function `has_api<A>(at: &BlockId)` to
/// check if the runtime at the given block id implements the requested runtime api trait.
pub use sp_api_proc_macro::decl_runtime_apis;

/// Tags given trait implementations as runtime apis.
///
/// All traits given to this macro, need to be declared with the
/// [`decl_runtime_apis!`](macro.decl_runtime_apis.html) macro. The implementation of the trait
/// should follow the declaration given to the [`decl_runtime_apis!`](macro.decl_runtime_apis.html)
/// macro, besides the `Block` type that is required as first generic parameter for each runtime
/// api trait. When implementing a runtime api trait, it is required that the trait is referenced
/// by a path, e.g. `impl my_trait::MyTrait for Runtime`. The macro will use this path to access
/// the declaration of the trait for the runtime side.
///
/// The macro also generates the api implementations for the client side and provides it through
/// the `RuntimeApi` type. The `RuntimeApi` is hidden behind a `feature` called `std`.
///
/// To expose version information about all implemented api traits, the constant
/// `RUNTIME_API_VERSIONS` is generated. This constant should be used to instantiate the `apis`
/// field of `RuntimeVersion`.
///
/// # Example
///
/// ```rust
/// use sp_version::create_runtime_str;
/// #
/// # use sp_runtime::traits::{GetNodeBlockType, Block as BlockT};
/// # use sp_test_primitives::Block;
/// #
/// # /// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
/// # /// trait are done by the `construct_runtime!` macro in a real runtime.
/// # pub struct Runtime {}
/// # impl GetNodeBlockType for Runtime {
/// #     type NodeBlock = Block;
/// # }
/// #
/// # sp_api::decl_runtime_apis! {
/// #     /// Declare the api trait.
/// #     pub trait Balance {
/// #         /// Get the balance.
/// #         fn get_balance() -> u64;
/// #         /// Set the balance.
/// #         fn set_balance(val: u64);
/// #     }
/// #     pub trait BlockBuilder {
/// #        fn build_block() -> Block;
/// #     }
/// # }
///
/// /// All runtime api implementations need to be done in one call of the macro!
/// sp_api::impl_runtime_apis! {
/// #   impl sp_api::Core<Block> for Runtime {
/// #       fn version() -> sp_version::RuntimeVersion {
/// #           unimplemented!()
/// #       }
/// #       fn execute_block(_block: Block) {}
/// #       fn initialize_block(_header: &<Block as BlockT>::Header) {}
/// #   }
///
///     impl self::Balance<Block> for Runtime {
///         fn get_balance() -> u64 {
///             1
///         }
///         fn set_balance(_bal: u64) {
///             // Store the balance
///         }
///     }
///
///     impl self::BlockBuilder<Block> for Runtime {
///         fn build_block() -> Block {
///              unimplemented!("Please implement me!")
///         }
///     }
/// }
///
/// /// Runtime version. This needs to be declared for each runtime.
/// pub const VERSION: sp_version::RuntimeVersion = sp_version::RuntimeVersion {
///     spec_name: create_runtime_str!("node"),
///     impl_name: create_runtime_str!("test-node"),
///     authoring_version: 1,
///     spec_version: 1,
///     impl_version: 0,
///     // Here we are exposing the runtime api versions.
///     apis: RUNTIME_API_VERSIONS,
///     transaction_version: 1,
/// };
///
/// # fn main() {}
/// ```
pub use sp_api_proc_macro::impl_runtime_apis;

/// Mocks given trait implementations as runtime apis.
///
/// Accepts similar syntax as [`impl_runtime_apis!`](macro.impl_runtime_apis.html) and generates
/// simplified mock implementations of the given runtime apis. The difference in syntax is that the
/// trait does not need to be referenced by a qualified path, methods accept the `&self` parameter
/// and the error type can be specified as associated type. If no error type is specified `String`
/// is used as error type.
///
/// Besides implementing the given traits, the [`Core`], [`ApiExt`] and [`ApiErrorExt`] are
/// implemented automatically.
///
/// # Example
///
/// ```rust
/// use sp_version::create_runtime_str;
/// #
/// # use sp_runtime::traits::Block as BlockT;
/// # use sp_test_primitives::Block;
/// #
/// # sp_api::decl_runtime_apis! {
/// #     /// Declare the api trait.
/// #     pub trait Balance {
/// #         /// Get the balance.
/// #         fn get_balance() -> u64;
/// #         /// Set the balance.
/// #         fn set_balance(val: u64);
/// #     }
/// #     pub trait BlockBuilder {
/// #        fn build_block() -> Block;
/// #     }
/// # }
///
/// struct MockApi {
///     balance: u64,
/// }
///
/// /// All runtime api mock implementations need to be done in one call of the macro!
/// sp_api::mock_impl_runtime_apis! {
///     impl Balance<Block> for MockApi {
///         /// Here we take the `&self` to access the instance.
///         fn get_balance(&self) -> u64 {
///             self.balance
///         }
///         fn set_balance(_bal: u64) {
///             // Store the balance
///         }
///     }
///
///     impl BlockBuilder<Block> for MockApi {
///         /// Sets the error type that is being used by the mock implementation.
///         /// The error type is used by all runtime apis. It is only required to
///         /// be specified in one trait implementation.
///         type Error = String;
///
///         fn build_block() -> Block {
///              unimplemented!("Not Required in tests")
///         }
///     }
/// }
///
/// # fn main() {}
/// ```
pub use sp_api_proc_macro::mock_impl_runtime_apis;

/// A type that records all accessed trie nodes and generates a proof out of it.
#[cfg(feature = "std")]
pub type ProofRecorder<B> = sp_state_machine::ProofRecorder<HashFor<B>>;

/// A type that is used as cache for the storage transactions.
#[cfg(feature = "std")]
pub type StorageTransactionCache<Block, Backend> =
	sp_state_machine::StorageTransactionCache<
		<Backend as StateBackend<HashFor<Block>>>::Transaction, HashFor<Block>, NumberFor<Block>
	>;

#[cfg(feature = "std")]
pub type StorageChanges<SBackend, Block> =
	sp_state_machine::StorageChanges<
		<SBackend as StateBackend<HashFor<Block>>>::Transaction,
		HashFor<Block>,
		NumberFor<Block>
	>;

/// Extract the state backend type for a type that implements `ProvideRuntimeApi`.
#[cfg(feature = "std")]
pub type StateBackendFor<P, Block> =
	<<P as ProvideRuntimeApi<Block>>::Api as ApiExt<Block>>::StateBackend;

/// Extract the state backend transaction type for a type that implements `ProvideRuntimeApi`.
#[cfg(feature = "std")]
pub type TransactionFor<P, Block> =
	<StateBackendFor<P, Block> as StateBackend<HashFor<Block>>>::Transaction;

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
	type StateBackend: StateBackend<HashFor<Block>>;

	/// Execute the given closure inside a new transaction.
	///
	/// Depending on the outcome of the closure, the transaction is committed or rolled-back.
	///
	/// The internal result of the closure is returned afterwards.
	fn execute_in_transaction<F: FnOnce(&Self) -> TransactionOutcome<R>, R>(
		&self,
		call: F,
	) -> R where Self: Sized;

	/// Checks if the given api is implemented and versions match.
	fn has_api<A: RuntimeApiInfo + ?Sized>(
		&self,
		at: &BlockId<Block>,
	) -> Result<bool, Self::Error> where Self: Sized;

	/// Check if the given api is implemented and the version passes a predicate.
	fn has_api_with<A: RuntimeApiInfo + ?Sized, P: Fn(u32) -> bool>(
		&self,
		at: &BlockId<Block>,
		pred: P,
	) -> Result<bool, Self::Error> where Self: Sized;

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
	///
	/// After executing this function, all collected changes are reset.
	fn into_storage_changes(
		&self,
		backend: &Self::StateBackend,
		changes_trie_state: Option<&ChangesTrieState<HashFor<Block>, NumberFor<Block>>>,
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
pub struct CallApiAtParams<'a, Block: BlockT, C, NC, Backend: StateBackend<HashFor<Block>>> {
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
	/// The overlayed changes to be applied to the offchain worker database.
	pub offchain_changes: &'a RefCell<OffchainOverlayedChanges>,
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
	type StateBackend: StateBackend<HashFor<Block>>;

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
pub struct ApiRef<'a, T>(T, std::marker::PhantomData<&'a ()>);

#[cfg(feature = "std")]
impl<'a, T> From<T> for ApiRef<'a, T> {
	fn from(api: T) -> Self {
		ApiRef(api, Default::default())
	}
}

#[cfg(feature = "std")]
impl<'a, T> std::ops::Deref for ApiRef<'a, T> {
	type Target = T;

	fn deref(&self) -> &Self::Target {
		&self.0
	}
}

#[cfg(feature = "std")]
impl<'a, T> std::ops::DerefMut for ApiRef<'a, T> {
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

#[derive(codec::Encode, codec::Decode)]
pub struct OldRuntimeVersion {
	pub spec_name: RuntimeString,
	pub impl_name: RuntimeString,
	pub authoring_version: u32,
	pub spec_version: u32,
	pub impl_version: u32,
	pub apis: ApisVec,
}

impl From<OldRuntimeVersion> for RuntimeVersion {
	fn from(x: OldRuntimeVersion) -> Self {
		Self {
			spec_name: x.spec_name,
			impl_name: x.impl_name,
			authoring_version: x.authoring_version,
			spec_version: x.spec_version,
			impl_version: x.impl_version,
			apis: x.apis,
			transaction_version: 1,
		}
	}
}

impl From<RuntimeVersion> for OldRuntimeVersion {
	fn from(x: RuntimeVersion) -> Self {
		Self {
			spec_name: x.spec_name,
			impl_name: x.impl_name,
			authoring_version: x.authoring_version,
			spec_version: x.spec_version,
			impl_version: x.impl_version,
			apis: x.apis,
		}
	}
}

decl_runtime_apis! {
	/// The `Core` runtime api that every Substrate runtime needs to implement.
	#[core_trait]
	#[api_version(3)]
	pub trait Core {
		/// Returns the version of the runtime.
		fn version() -> RuntimeVersion;
		/// Returns the version of the runtime.
		#[changed_in(3)]
		fn version() -> OldRuntimeVersion;
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
