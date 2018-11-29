// Copyright 2018 Parity Technologies (UK) Ltd.
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

//! Macros for declaring and implementing runtime apis.

#![recursion_limit = "128"]
extern crate proc_macro;
extern crate proc_macro2;
extern crate quote;
extern crate syn;

use proc_macro::TokenStream;

mod impl_runtime_apis;
mod decl_runtime_apis;
mod utils;
mod compile_fail_tests;

/// Tags given trait implementations as runtime apis.
///
/// All traits given to this macro, need to be declared with the `decl_runtime_apis!` macro.
/// The implementation of the trait should follow the declaration given to the `decl_runtime_apis!`
/// macro, besides the `Block` type that is required as first generic parameter for each runtime
/// api trait. When implementing a runtime api trait, it is required that the trait is referenced
/// by a path, e.g. `impl my_trait::MyTrait for Runtime`. The macro will use this path to access
/// the declaration of the trait for the runtime side.
///
/// The macro also generates the implementation of the apis for the client side by generating the
/// `RuntimeApi` type. The `RuntimeApi` is hidden behind a `feature` called `std`.
///
/// # Example
///
/// ```rust
/// #[macro_use]
/// extern crate substrate_client;
/// # extern crate sr_primitives as runtime_primitives;
/// # extern crate substrate_primitives as primitives;
/// # #[macro_use]
/// # extern crate parity_codec_derive;
/// # extern crate serde;
/// # extern crate core;
/// #
/// # use primitives::hash::H256;
/// # use runtime_primitives::traits::{BlakeTwo256, GetNodeBlockType, Extrinsic as ExtrinsicT};
/// #
/// # // All the stuff we need to declare our `Block`
/// # pub type BlockNumber = u64;
/// # pub type DigestItem = runtime_primitives::generic::DigestItem<H256, u64>;
/// # pub type Digest = runtime_primitives::generic::Digest<DigestItem>;
/// # #[derive(Clone, PartialEq, Eq, Encode, Decode, Debug)]
/// # pub struct Extrinsic {}
/// #
/// # impl serde::Serialize for Extrinsic {
/// #     fn serialize<S>(&self, seq: S) -> Result<S::Ok, S::Error> where S: ::serde::Serializer {
/// #         unimplemented!()
/// #     }
/// # }
/// # impl ExtrinsicT for Extrinsic {
/// #     fn is_signed(&self) -> Option<bool> {
/// #         unimplemented!()
/// #     }
/// # }
/// # pub type Header = runtime_primitives::generic::Header<BlockNumber, BlakeTwo256, DigestItem>;
/// # pub type Block = runtime_primitives::generic::Block<Header, Extrinsic>;
/// #
/// # /// The declaration of the `Runtime` type and the implementation of the `GetNodeBlockType`
/// # /// trait are done by the `construct_runtime!` macro in a real runtime.
/// # struct Runtime {}
/// # impl GetNodeBlockType for Runtime {
/// #     type NodeBlock = Block;
/// # }
/// #
/// # decl_runtime_apis! {
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
/// impl_runtime_apis! {
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
/// #[macro_use]
/// extern crate substrate_client;
///
/// decl_runtime_apis! {
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
#[proc_macro]
pub fn decl_runtime_apis(input: TokenStream) -> TokenStream {
	decl_runtime_apis::decl_runtime_apis_impl(input)
}
