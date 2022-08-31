// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Macros for declaring and implementing runtime apis.

#![recursion_limit = "512"]

use proc_macro::TokenStream;

mod impl_runtime_apis;
mod decl_runtime_apis;
mod utils;

/// Tags given trait implementations as runtime apis.
///
/// All traits given to this macro, need to be declared with the `decl_runtime_apis!` macro.
/// The implementation of the trait should follow the declaration given to the `decl_runtime_apis!`
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
/// # use test_client::runtime::Block;
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
/// #    }
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
#[proc_macro]
pub fn impl_runtime_apis(input: TokenStream) -> TokenStream {
	impl_runtime_apis::impl_runtime_apis_impl(input)
}

/// Declares given traits as runtime apis.
///
/// The macro will create two declarations, one for using on the client side and one for using
/// on the runtime side. The declaration for the runtime side is hidden in its own module.
/// The client side declaration gets two extra parameters per function,
/// `&self` and `at: &BlockId<Block>`. The runtime side declaration will match the given trait
/// declaration. Besides one exception, the macro adds an extra generic parameter `Block: BlockT`
/// to the client side and the runtime side. This generic parameter is usable by the user.
///
/// For implementing these macros you should use the `impl_runtime_apis!` macro.
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
/// spec version!). Such a method also does not need to be implemented in the runtime.
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
#[proc_macro]
pub fn decl_runtime_apis(input: TokenStream) -> TokenStream {
	decl_runtime_apis::decl_runtime_apis_impl(input)
}
