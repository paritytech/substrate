// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Proc macro of Support code for the runtime.

#![recursion_limit = "512"]

mod benchmark;
mod clone_no_bound;
mod construct_runtime;
mod crate_version;
mod debug_no_bound;
mod default_no_bound;
mod dummy_part_checker;
mod key_prefix;
mod match_and_insert;
mod pallet;
mod pallet_error;
mod partial_eq_no_bound;
mod storage;
mod storage_alias;
mod transactional;
mod tt_macro;

use proc_macro::TokenStream;
use quote::quote;
use std::{cell::RefCell, str::FromStr};
pub(crate) use storage::INHERENT_INSTANCE_NAME;

thread_local! {
	/// A global counter, can be used to generate a relatively unique identifier.
	static COUNTER: RefCell<Counter> = RefCell::new(Counter(0));
}

/// Counter to generate a relatively unique identifier for macros. This is necessary because
/// declarative macros gets hoisted to the crate root, which shares the namespace with other pallets
/// containing the very same macros.
struct Counter(u64);

impl Counter {
	fn inc(&mut self) -> u64 {
		let ret = self.0;
		self.0 += 1;
		ret
	}
}

/// Get the value from the given environment variable set by cargo.
///
/// The value is parsed into the requested destination type.
fn get_cargo_env_var<T: FromStr>(version_env: &str) -> std::result::Result<T, ()> {
	let version = std::env::var(version_env)
		.unwrap_or_else(|_| panic!("`{}` is always set by cargo; qed", version_env));

	T::from_str(&version).map_err(drop)
}

/// Generate the counter_prefix related to the storage.
/// counter_prefix is used by counted storage map.
fn counter_prefix(prefix: &str) -> String {
	format!("CounterFor{}", prefix)
}

/// Declares strongly-typed wrappers around codec-compatible types in storage.
///
/// ## Example
///
/// ```nocompile
/// decl_storage! {
/// 	trait Store for Module<T: Config> as Example {
/// 		Foo get(fn foo) config(): u32=12;
/// 		Bar: map hasher(identity) u32 => u32;
/// 		pub Zed build(|config| vec![(0, 0)]): map hasher(identity) u32 => u32;
/// 	}
/// }
/// ```
///
/// Declaration is set with the header `(pub) trait Store for Module<T: Config> as Example`,
/// with `Store` a (pub) trait generated associating each storage item to the `Module` and
/// `as Example` setting the prefix used for storage items of this module. `Example` must be unique:
/// another module with the same name and the same inner storage item name will conflict.
/// `Example` is called the module prefix.
///
/// note: For instantiable modules the module prefix is prepended with instance
/// prefix. Instance prefix is "" for default instance and "Instance$n" for instance number $n.
/// Thus, instance 3 of module Example has a module prefix of `Instance3Example`
///
/// Basic storage consists of a name and a type; supported types are:
///
/// * Value: `Foo: type`: Implements the
///   [`StorageValue`](../frame_support/storage/trait.StorageValue.html) trait using the
///   [`StorageValue generator`](../frame_support/storage/generator/trait.StorageValue.html).
///
///   The generator is implemented with:
///   * `module_prefix`: module_prefix
///   * `storage_prefix`: storage_name
///
///   Thus the storage value is finally stored at:
///   ```nocompile
///   Twox128(module_prefix) ++ Twox128(storage_prefix)
///   ```
///
/// * Map: `Foo: map hasher($hash) type => type`: Implements the
///   [`StorageMap`](../frame_support/storage/trait.StorageMap.html) trait using the [`StorageMap
///   generator`](../frame_support/storage/generator/trait.StorageMap.html). And
///   [`StoragePrefixedMap`](../frame_support/storage/trait.StoragePrefixedMap.html).
///
///   `$hash` representing a choice of hashing algorithms available in the
///   [`Hashable`](../frame_support/trait.Hashable.html) trait. You will generally want to use one
///   of three hashers:
///   * `blake2_128_concat`: The default, safe choice. Use if you are unsure or don't care. It is
///     secure against user-tainted keys, fairly fast and memory-efficient and supports iteration
///     over its keys and values. This must be used if the keys of your map can be selected *en
///     masse* by untrusted users.
///   * `twox_64_concat`: This is an insecure hasher and can only be used safely if you know that
///     the preimages cannot be chosen at will by untrusted users. It is memory-efficient, extremely
///     performant and supports iteration over its keys and values. You can safely use this is the
///     key is:
///     - A (slowly) incrementing index.
///     - Known to be the result of a cryptographic hash (though `identity` is a better choice
///       here).
///     - Known to be the public key of a cryptographic key pair in existence.
///   * `identity`: This is not a hasher at all, and just uses the key material directly. Since it
///     does no hashing or appending, it's the fastest possible hasher, however, it's also the least
///     secure. It can be used only if you know that the key will be cryptographically/securely
///     randomly distributed over the binary encoding space. In most cases this will not be true.
///     One case where it is true, however, if where the key is itself the result of a cryptographic
///     hash of some existent data.
///
///   Other hashers will tend to be "opaque" and not support iteration over the keys in the
///   map. It is not recommended to use these.
///
///   The generator is implemented with:
///   * `module_prefix`: $module_prefix
///   * `storage_prefix`: storage_name
///   * `Hasher`: $hash
///
///   Thus the keys are stored at:
///   ```nocompile
///   twox128(module_prefix) ++ twox128(storage_prefix) ++ hasher(encode(key))
///   ```
///
/// * Double map: `Foo: double_map hasher($hash1) u32, hasher($hash2) u32 => u32`: Implements the
///   [`StorageDoubleMap`](../frame_support/storage/trait.StorageDoubleMap.html) trait using the
///   [`StorageDoubleMap
///   generator`](../frame_support/storage/generator/trait.StorageDoubleMap.html). And
///   [`StoragePrefixedMap`](../frame_support/storage/trait.StoragePrefixedMap.html).
///
///   `$hash1` and `$hash2` representing choices of hashing algorithms available in the
///   [`Hashable`](../frame_support/trait.Hashable.html) trait. They must be chosen with care, see
///   generator documentation.
///
///   The generator is implemented with:
///   * `module_prefix`: $module_prefix
///   * `storage_prefix`: storage_name
///   * `Hasher1`: $hash1
///   * `Hasher2`: $hash2
///
///   Thus keys are stored at:
///   ```nocompile
///   Twox128(module_prefix) ++ Twox128(storage_prefix) ++ Hasher1(encode(key1)) ++
/// Hasher2(encode(key2))   ```
///
/// Supported hashers (ordered from least to best security):
///
/// * `identity` - Just the unrefined key material. Use only when it is known to be a secure hash
///   already. The most efficient and iterable over keys.
/// * `twox_64_concat` - TwoX with 64bit + key concatenated. Use only when an untrusted source
///   cannot select and insert key values. Very efficient and iterable over keys.
/// * `blake2_128_concat` - Blake2 with 128bit + key concatenated. Slower but safe to use in all
///   circumstances. Iterable over keys.
///
/// Deprecated hashers, which do not support iteration over keys include:
/// * `twox_128` - TwoX with 128bit.
/// * `twox_256` - TwoX with with 256bit.
/// * `blake2_128` - Blake2 with 128bit.
/// * `blake2_256` - Blake2 with 256bit.
///
/// Basic storage can be extended as such:
///
/// `#vis #name get(fn #getter) config(#field_name) build(#closure): #type = #default;`
///
/// * `#vis`: Set the visibility of the structure. `pub` or nothing.
/// * `#name`: Name of the storage item, used as a prefix in storage.
/// * \[optional\] `get(fn #getter)`: Implements the function #getter to `Module`.
/// * \[optional\] `config(#field_name)`: `field_name` is optional if get is set.
/// Will include the item in `GenesisConfig`.
/// * \[optional\] `build(#closure)`: Closure called with storage overlays.
/// * \[optional\] `max_values(#expr)`: `expr` is an expression returning a `u32`. It is used to
/// implement `StorageInfoTrait`. Note this attribute is not available for storage value as the
/// maximum number of values is 1.
/// * `#type`: Storage type.
/// * \[optional\] `#default`: Value returned when none.
///
/// Storage items are accessible in multiple ways:
///
/// * The structure: `Foo` or `Foo::<T>` depending if the value type is generic or not.
/// * The `Store` trait structure: `<Module<T> as Store>::Foo`
/// * The getter on the module that calls get on the structure: `Module::<T>::foo()`
///
/// ## GenesisConfig
///
/// An optional `GenesisConfig` struct for storage initialization can be defined, either
/// when at least one storage field requires default initialization
/// (both `get` and `config` or `build`), or specifically as in:
///
/// ```nocompile
/// decl_storage! {
/// 	trait Store for Module<T: Config> as Example {
///
/// 		// Your storage items
/// 	}
/// 		add_extra_genesis {
/// 			config(genesis_field): GenesisFieldType;
/// 			config(genesis_field2): GenesisFieldType;
/// 			...
/// 			build(|_: &Self| {
/// 				// Modification of storage
/// 			})
/// 		}
/// }
/// ```
///
/// This struct can be exposed as `ExampleConfig` by the `construct_runtime!` macro like follows:
///
/// ```nocompile
/// construct_runtime!(
/// 	pub enum Runtime with ... {
///         ...,
///         Example: example::{Pallet, Storage, ..., Config<T>},
///         ...,
/// 	}
/// );
/// ```
///
/// ### Module with Instances
///
/// The `decl_storage!` macro supports building modules with instances with the following syntax
/// (`DefaultInstance` type is optional):
///
/// ```nocompile
/// trait Store for Module<T: Config<I>, I: Instance=DefaultInstance> as Example {}
/// ```
///
/// Accessing the structure no requires the instance as generic parameter:
/// * `Foo::<I>` if the value type is not generic
/// * `Foo::<T, I>` if the value type is generic
///
/// ## Where clause
///
/// This macro supports a where clause which will be replicated to all generated types.
///
/// ```nocompile
/// trait Store for Module<T: Config> as Example where T::AccountId: std::fmt::Display {}
/// ```
///
/// ## Limitations
///
/// # Instancing and generic `GenesisConfig`
///
/// If your module supports instancing and you see an error like `parameter `I` is never used` for
/// your `decl_storage!`, you are hitting a limitation of the current implementation. You probably
/// try to use an associated type of a non-instantiable trait. To solve this, add the following to
/// your macro call:
///
/// ```nocompile
/// add_extra_genesis {
/// 	config(phantom): std::marker::PhantomData<I>,
/// }
/// ```
///
/// This adds a field to your `GenesisConfig` with the name `phantom` that you can initialize with
/// `Default::default()`.
///
/// ## PoV information
///
/// To implement the trait `StorageInfoTrait` for storages an additional attribute can be used
/// `generate_storage_info`:
/// ```nocompile
/// decl_storage! { generate_storage_info
/// 	trait Store for ...
/// }
/// ```
#[proc_macro]
pub fn decl_storage(input: TokenStream) -> TokenStream {
	storage::decl_storage_impl(input)
}

/// Construct a runtime, with the given name and the given pallets.
///
/// The parameters here are specific types for `Block`, `NodeBlock`, and `UncheckedExtrinsic`
/// and the pallets that are used by the runtime.
/// `Block` is the block type that is used in the runtime and `NodeBlock` is the block type
/// that is used in the node. For instance they can differ in the extrinsics type.
///
/// # Example:
///
/// ```ignore
/// construct_runtime!(
///     pub enum Runtime where
///         Block = Block,
///         NodeBlock = node::Block,
///         UncheckedExtrinsic = UncheckedExtrinsic
///     {
///         System: frame_system::{Pallet, Call, Event<T>, Config<T>} = 0,
///         Test: path::to::test::{Pallet, Call} = 1,
///
///         // Pallets with instances.
///         Test2_Instance1: test2::<Instance1>::{Pallet, Call, Storage, Event<T, I>, Config<T, I>, Origin<T, I>},
///         Test2_DefaultInstance: test2::{Pallet, Call, Storage, Event<T>, Config<T>, Origin<T>} = 4,
///
///         // Pallets declared with `pallet` attribute macro: no need to define the parts
///         Test3_Instance1: test3::<Instance1>,
///         Test3_DefaultInstance: test3,
///
///         // with `exclude_parts` keyword some part can be excluded.
///         Test4_Instance1: test4::<Instance1> exclude_parts { Call, Origin },
///         Test4_DefaultInstance: test4 exclude_parts { Storage },
///
///         // with `use_parts` keyword, a subset of the pallet parts can be specified.
///         Test4_Instance1: test4::<Instance1> use_parts { Pallet, Call},
///         Test4_DefaultInstance: test4 use_parts { Pallet },
///     }
/// )
/// ```
///
/// Each pallet is declared as such:
/// * `Identifier`: name given to the pallet that uniquely identifies it.
///
/// * `:`: colon separator
///
/// * `path::to::pallet`: identifiers separated by colons which declare the path to a pallet
///   definition.
///
/// * `::<InstanceN>` optional: specify the instance of the pallet to use. If not specified it will
///   use the default instance (or the only instance in case of non-instantiable pallets).
///
/// * `::{ Part1, Part2<T>, .. }` optional if pallet declared with `frame_support::pallet`: Comma
///   separated parts declared with their generic. If a pallet is declared with
///   `frame_support::pallet` macro then the parts can be automatically derived if not explicitly
///   provided. We provide support for the following module parts in a pallet:
///
///   - `Pallet` - Required for all pallets
///   - `Call` - If the pallet has callable functions
///   - `Storage` - If the pallet uses storage
///   - `Event` or `Event<T>` (if the event is generic) - If the pallet emits events
///   - `Origin` or `Origin<T>` (if the origin is generic) - If the pallet has instanciable origins
///   - `Config` or `Config<T>` (if the config is generic) - If the pallet builds the genesis
///     storage with `GenesisConfig`
///   - `Inherent` - If the pallet provides/can check inherents.
///   - `ValidateUnsigned` - If the pallet validates unsigned extrinsics.
///
///   It is important to list these parts here to export them correctly in the metadata or to make
/// the pallet usable in the runtime.
///
/// * `exclude_parts { Part1, Part2 }` optional: comma separated parts without generics. I.e. one of
///   `Pallet`, `Call`, `Storage`, `Event`, `Origin`, `Config`, `Inherent`, `ValidateUnsigned`. It
///   is incompatible with `use_parts`. This specifies the part to exclude. In order to select
///   subset of the pallet parts.
///
///   For example excluding the part `Call` can be useful if the runtime doesn't want to make the
///   pallet calls available.
///
/// * `use_parts { Part1, Part2 }` optional: comma separated parts without generics. I.e. one of
///   `Pallet`, `Call`, `Storage`, `Event`, `Origin`, `Config`, `Inherent`, `ValidateUnsigned`. It
///   is incompatible with `exclude_parts`. This specifies the part to use. In order to select a
///   subset of the pallet parts.
///
///   For example not using the part `Call` can be useful if the runtime doesn't want to make the
///   pallet calls available.
///
/// * `= $n` optional: number to define at which index the pallet variants in `OriginCaller`, `Call`
///   and `Event` are encoded, and to define the ModuleToIndex value.
///
///   if `= $n` is not given, then index is resolved in the same way as fieldless enum in Rust
///   (i.e. incrementedly from previous index):
///   ```nocompile
///   pallet1 .. = 2,
///   pallet2 .., // Here pallet2 is given index 3
///   pallet3 .. = 0,
///   pallet4 .., // Here pallet4 is given index 1
///   ```
///
/// # Note
///
/// The population of the genesis storage depends on the order of pallets. So, if one of your
/// pallets depends on another pallet, the pallet that is depended upon needs to come before
/// the pallet depending on it.
///
/// # Type definitions
///
/// * The macro generates a type alias for each pallet to their `Pallet`. E.g. `type System =
///   frame_system::Pallet<Runtime>`
#[proc_macro]
pub fn construct_runtime(input: TokenStream) -> TokenStream {
	construct_runtime::construct_runtime(input)
}

/// The pallet struct placeholder `#[pallet::pallet]` is mandatory and allows you to specify
/// pallet information.
///
/// The struct must be defined as follows:
/// ```ignore
/// #[pallet::pallet]
/// pub struct Pallet<T>(_);
/// ```
/// I.e. a regular struct definition named `Pallet`, with generic T and no where clause.
///
/// ## Macro expansion:
///
/// The macro adds this attribute to the struct definition:
/// ```ignore
/// #[derive(
/// 	frame_support::CloneNoBound,
/// 	frame_support::EqNoBound,
/// 	frame_support::PartialEqNoBound,
/// 	frame_support::RuntimeDebugNoBound,
/// )]
/// ```
/// and replaces the type `_` with `PhantomData<T>`. It also implements on the pallet:
/// * `GetStorageVersion`
/// * `OnGenesis`: contains some logic to write the pallet version into storage.
/// * `PalletErrorTypeInfo`: provides the type information for the pallet error, if defined.
///
/// It declares `type Module` type alias for `Pallet`, used by `construct_runtime`.
///
/// It implements `PalletInfoAccess` on `Pallet` to ease access to pallet information given by
/// `frame_support::traits::PalletInfo`. (The implementation uses the associated type
/// `frame_system::Config::PalletInfo`).
///
/// It implements `StorageInfoTrait` on `Pallet` which give information about all storages.
///
/// If the attribute `generate_store` is set then the macro creates the trait `Store` and
/// implements it on `Pallet`.
///
/// If the attribute `set_storage_max_encoded_len` is set then the macro calls
/// `StorageInfoTrait` for each storage in the implementation of `StorageInfoTrait` for the
/// pallet. Otherwise it implements `StorageInfoTrait` for the pallet using the
/// `PartialStorageInfoTrait` implementation of storages.
///
/// ## Dev Mode (`#[pallet(dev_mode)]`)
///
/// Specifying the argument `dev_mode` will allow you to enable dev mode for a pallet. The aim
/// of dev mode is to loosen some of the restrictions and requirements placed on production
/// pallets for easy tinkering and development. Dev mode pallets should not be used in
/// production. Enabling dev mode has the following effects:
///
/// * Weights no longer need to be specified on every `#[pallet::call]` declaration. By default, dev
///   mode pallets will assume a weight of zero (`0`) if a weight is not specified. This is
///   equivalent to specifying `#[weight(0)]` on all calls that do not specify a weight.
/// * All storages are marked as unbounded, meaning you do not need to implement `MaxEncodedLen` on
///   storage types. This is equivalent to specifying `#[pallet::unbounded]` on all storage type
///   definitions.
///
/// Note that the `dev_mode` argument can only be supplied to the `#[pallet]` or
/// `#[frame_support::pallet]` attribute macro that encloses your pallet module. This argument
/// cannot be specified anywhere else, including but not limited to the `#[pallet::pallet]`
/// attribute macro.
///
/// <div class="example-wrap" style="display:inline-block"><pre class="compile_fail"
/// style="white-space:normal;font:inherit;">
/// <strong>WARNING</strong>:
/// You should not deploy or use dev mode pallets in production. Doing so can break your chain
/// and therefore should never be done. Once you are done tinkering, you should remove the
/// 'dev_mode' argument from your #[pallet] declaration and fix any compile errors before
/// attempting to use your pallet in a production scenario.
/// </pre></div>
///
/// See `frame_support::pallet` docs for more info.
///
/// ## Runtime Metadata Documentation
///
/// The documentation added to this pallet is included in the runtime metadata.
///
/// The documentation can be defined in the following ways:
///
/// ```ignore
/// #[pallet::pallet]
/// /// Documentation for pallet 1
/// #[doc = "Documentation for pallet 2"]
/// #[doc = include_str!("../README.md")]
/// #[pallet_doc("../doc1.md")]
/// #[pallet_doc("../doc2.md")]
/// pub struct Pallet<T>(_);
/// ```
///
/// The runtime metadata for this pallet contains the following
///  - " Documentation for pallet 1" (captured from `///`)
///  - "Documentation for pallet 2"  (captured from `#[doc]`)
///  - content of ../README.md       (captured from `#[doc]` with `include_str!`)
///  - content of "../doc1.md"       (captured from `pallet_doc`)
///  - content of "../doc2.md"       (captured from `pallet_doc`)
///
/// ### `doc` attribute
///
/// The value of the `doc` attribute is included in the runtime metadata, as well as
/// expanded on the pallet module. The previous example is expanded to:
///
/// ```ignore
/// /// Documentation for pallet 1
/// /// Documentation for pallet 2
/// /// Content of README.md
/// pub struct Pallet<T>(_);
/// ```
///
/// If you want to specify the file from which the documentation is loaded, you can use the
/// `include_str` macro. However, if you only want the documentation to be included in the
/// runtime metadata, use the `pallet_doc` attribute.
///
/// ### `pallet_doc` attribute
///
/// Unlike the `doc` attribute, the documentation provided to the `pallet_doc` attribute is
/// not inserted on the module.
///
/// The `pallet_doc` attribute can only be provided with one argument,
/// which is the file path that holds the documentation to be added to the metadata.
///
/// This approach is beneficial when you use the `include_str` macro at the beginning of the file
/// and want that documentation to extend to the runtime metadata, without reiterating the
/// documentation on the module itself.
#[proc_macro_attribute]
pub fn pallet(attr: TokenStream, item: TokenStream) -> TokenStream {
	pallet::pallet(attr, item)
}

/// An attribute macro that can be attached to a (non-empty) module declaration. Doing so will
/// designate that module as a benchmarking module.
///
/// See `frame_benchmarking::v2` for more info.
#[proc_macro_attribute]
pub fn benchmarks(attr: TokenStream, tokens: TokenStream) -> TokenStream {
	match benchmark::benchmarks(attr, tokens, false) {
		Ok(tokens) => tokens,
		Err(err) => err.to_compile_error().into(),
	}
}

/// An attribute macro that can be attached to a (non-empty) module declaration. Doing so will
/// designate that module as an instance benchmarking module.
///
/// See `frame_benchmarking::v2` for more info.
#[proc_macro_attribute]
pub fn instance_benchmarks(attr: TokenStream, tokens: TokenStream) -> TokenStream {
	match benchmark::benchmarks(attr, tokens, true) {
		Ok(tokens) => tokens,
		Err(err) => err.to_compile_error().into(),
	}
}

/// An attribute macro used to declare a benchmark within a benchmarking module. Must be
/// attached to a function definition containing an `#[extrinsic_call]` or `#[block]`
/// attribute.
///
/// See `frame_benchmarking::v2` for more info.
#[proc_macro_attribute]
pub fn benchmark(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
	quote!(compile_error!(
		"`#[benchmark]` must be in a module labeled with #[benchmarks] or #[instance_benchmarks]."
	))
	.into()
}

/// An attribute macro used to specify the extrinsic call inside a benchmark function, and also
/// used as a boundary designating where the benchmark setup code ends, and the benchmark
/// verification code begins.
///
/// See `frame_benchmarking::v2` for more info.
#[proc_macro_attribute]
pub fn extrinsic_call(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
	quote!(compile_error!(
		"`#[extrinsic_call]` must be in a benchmark function definition labeled with `#[benchmark]`."
	);)
	.into()
}

/// An attribute macro used to specify that a block should be the measured portion of the
/// enclosing benchmark function, This attribute is also used as a boundary designating where
/// the benchmark setup code ends, and the benchmark verification code begins.
///
/// See `frame_benchmarking::v2` for more info.
#[proc_macro_attribute]
pub fn block(_attrs: TokenStream, _tokens: TokenStream) -> TokenStream {
	quote!(compile_error!(
		"`#[block]` must be in a benchmark function definition labeled with `#[benchmark]`."
	))
	.into()
}

/// Execute the annotated function in a new storage transaction.
///
/// The return type of the annotated function must be `Result`. All changes to storage performed
/// by the annotated function are discarded if it returns `Err`, or committed if `Ok`.
///
/// # Example
///
/// ```nocompile
/// #[transactional]
/// fn value_commits(v: u32) -> result::Result<u32, &'static str> {
/// 	Value::set(v);
/// 	Ok(v)
/// }
///
/// #[transactional]
/// fn value_rollbacks(v: u32) -> result::Result<u32, &'static str> {
/// 	Value::set(v);
/// 	Err("nah")
/// }
/// ```
#[proc_macro_attribute]
pub fn transactional(attr: TokenStream, input: TokenStream) -> TokenStream {
	transactional::transactional(attr, input).unwrap_or_else(|e| e.to_compile_error().into())
}

#[proc_macro_attribute]
pub fn require_transactional(attr: TokenStream, input: TokenStream) -> TokenStream {
	transactional::require_transactional(attr, input)
		.unwrap_or_else(|e| e.to_compile_error().into())
}

/// Derive [`Clone`] but do not bound any generic. Docs are at `frame_support::CloneNoBound`.
#[proc_macro_derive(CloneNoBound)]
pub fn derive_clone_no_bound(input: TokenStream) -> TokenStream {
	clone_no_bound::derive_clone_no_bound(input)
}

/// Derive [`Debug`] but do not bound any generics. Docs are at `frame_support::DebugNoBound`.
#[proc_macro_derive(DebugNoBound)]
pub fn derive_debug_no_bound(input: TokenStream) -> TokenStream {
	debug_no_bound::derive_debug_no_bound(input)
}

/// Derive [`Debug`], if `std` is enabled it uses `frame_support::DebugNoBound`, if `std` is not
/// enabled it just returns `"<stripped>"`.
/// This behaviour is useful to prevent bloating the runtime WASM blob from unneeded code.
#[proc_macro_derive(RuntimeDebugNoBound)]
pub fn derive_runtime_debug_no_bound(input: TokenStream) -> TokenStream {
	#[cfg(not(feature = "std"))]
	{
		let input: syn::DeriveInput = match syn::parse(input) {
			Ok(input) => input,
			Err(e) => return e.to_compile_error().into(),
		};

		let name = &input.ident;
		let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

		quote::quote!(
			const _: () = {
				impl #impl_generics core::fmt::Debug for #name #ty_generics #where_clause {
					fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
						fmt.write_str("<stripped>")
					}
				}
			};
		)
		.into()
	}

	#[cfg(feature = "std")]
	{
		debug_no_bound::derive_debug_no_bound(input)
	}
}

/// Derive [`PartialEq`] but do not bound any generic. Docs are at
/// `frame_support::PartialEqNoBound`.
#[proc_macro_derive(PartialEqNoBound)]
pub fn derive_partial_eq_no_bound(input: TokenStream) -> TokenStream {
	partial_eq_no_bound::derive_partial_eq_no_bound(input)
}

/// derive Eq but do no bound any generic. Docs are at `frame_support::EqNoBound`.
#[proc_macro_derive(EqNoBound)]
pub fn derive_eq_no_bound(input: TokenStream) -> TokenStream {
	let input: syn::DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

	quote::quote_spanned!(name.span() =>
		const _: () = {
			impl #impl_generics core::cmp::Eq for #name #ty_generics #where_clause {}
		};
	)
	.into()
}

/// derive `Default` but do no bound any generic. Docs are at `frame_support::DefaultNoBound`.
#[proc_macro_derive(DefaultNoBound, attributes(default))]
pub fn derive_default_no_bound(input: TokenStream) -> TokenStream {
	default_no_bound::derive_default_no_bound(input)
}

#[proc_macro]
pub fn crate_to_crate_version(input: TokenStream) -> TokenStream {
	crate_version::crate_to_crate_version(input)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

/// The number of module instances supported by the runtime, starting at index 1,
/// and up to `NUMBER_OF_INSTANCE`.
pub(crate) const NUMBER_OF_INSTANCE: u8 = 16;

/// This macro is meant to be used by frame-support only.
/// It implements the trait `HasKeyPrefix` and `HasReversibleKeyPrefix` for tuple of `Key`.
#[proc_macro]
pub fn impl_key_prefix_for_tuples(input: TokenStream) -> TokenStream {
	key_prefix::impl_key_prefix_for_tuples(input)
		.unwrap_or_else(syn::Error::into_compile_error)
		.into()
}

/// Internal macro use by frame_support to generate dummy part checker for old pallet declaration
#[proc_macro]
pub fn __generate_dummy_part_checker(input: TokenStream) -> TokenStream {
	dummy_part_checker::generate_dummy_part_checker(input)
}

/// Macro that inserts some tokens after the first match of some pattern.
///
/// # Example:
///
/// ```nocompile
/// match_and_insert!(
///     target = [{ Some content with { at some point match pattern } other match pattern are ignored }]
///     pattern = [{ match pattern }] // the match pattern cannot contain any group: `[]`, `()`, `{}`
/// 								  // can relax this constraint, but will require modifying the match logic in code
///     tokens = [{ expansion tokens }] // content inside braces can be anything including groups
/// );
/// ```
///
/// will generate:
///
/// ```nocompile
///     Some content with { at some point match pattern expansion tokens } other match patterns are
///     ignored
/// ```
#[proc_macro]
pub fn match_and_insert(input: TokenStream) -> TokenStream {
	match_and_insert::match_and_insert(input)
}

#[proc_macro_derive(PalletError, attributes(codec))]
pub fn derive_pallet_error(input: TokenStream) -> TokenStream {
	pallet_error::derive_pallet_error(input)
}

/// Internal macro used by `frame_support` to create tt-call-compliant macros
#[proc_macro]
pub fn __create_tt_macro(input: TokenStream) -> TokenStream {
	tt_macro::create_tt_return_macro(input)
}

#[proc_macro_attribute]
pub fn storage_alias(_: TokenStream, input: TokenStream) -> TokenStream {
	storage_alias::storage_alias(input.into())
		.unwrap_or_else(|r| r.into_compile_error())
		.into()
}

/// Used internally to decorate pallet attribute macro stubs when they are erroneously used
/// outside of a pallet module
fn pallet_macro_stub() -> TokenStream {
	quote!(compile_error!(
		"This attribute can only be used from within a pallet module marked with `#[frame_support::pallet]`"
	))
	.into()
}

/// The mandatory attribute `#[pallet::config]` defines the configurable options for the pallet.
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::config]
/// pub trait Config: frame_system::Config + $optionally_some_other_supertraits
/// $optional_where_clause
/// {
/// ...
/// }
/// ```
///
/// I.e. a regular trait definition named `Config`, with the supertrait
/// `frame_system::pallet::Config`, and optionally other supertraits and a where clause.
/// (Specifying other supertraits here is known as [tight
/// coupling](https://docs.substrate.io/reference/how-to-guides/pallet-design/use-tight-coupling/))
///
/// The associated type `RuntimeEvent` is reserved. If defined, it must have the bounds
/// `From<Event>` and `IsType<<Self as frame_system::Config>::RuntimeEvent>`.
///
/// [`pallet::event`](`macro@event`) must be present if `RuntimeEvent` exists as a config item
/// in your `#[pallet::config]`.
#[proc_macro_attribute]
pub fn config(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::constant]` attribute can be used to add an associated type trait bounded by `Get`
/// from [`pallet::config`](`macro@config`) into metadata, e.g.:
///
/// ```ignore
/// #[pallet::config]
/// pub trait Config: frame_system::Config {
/// 	#[pallet::constant]
/// 	type Foo: Get<u32>;
/// }
/// ```
#[proc_macro_attribute]
pub fn constant(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// To bypass the `frame_system::Config` supertrait check, use the attribute
/// `pallet::disable_frame_system_supertrait_check`, e.g.:
///
/// ```ignore
/// #[pallet::config]
/// #[pallet::disable_frame_system_supertrait_check]
/// pub trait Config: pallet_timestamp::Config {}
/// ```
///
/// NOTE: Bypassing the `frame_system::Config` supertrait check is typically desirable when you
/// want to write an alternative to the `frame_system` pallet.
#[proc_macro_attribute]
pub fn disable_frame_system_supertrait_check(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// To generate a `Store` trait associating all storages, annotate your `Pallet` struct with
/// the attribute `#[pallet::generate_store($vis trait Store)]`, e.g.:
///
/// ```ignore
/// #[pallet::pallet]
/// #[pallet::generate_store(pub(super) trait Store)]
/// pub struct Pallet<T>(_);
/// ```
/// More precisely, the `Store` trait contains an associated type for each storage. It is
/// implemented for `Pallet` allowing access to the storage from pallet struct.
///
/// Thus when defining a storage named `Foo`, it can later be accessed from `Pallet` using
/// `<Pallet as Store>::Foo`.
///
/// NOTE: this attribute is only valid when applied _directly_ to your `Pallet` struct
/// definition.
#[proc_macro_attribute]
pub fn generate_store(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// To generate the full storage info (used for PoV calculation) use the attribute
/// `#[pallet::generate_storage_info]`, e.g.:
///
/// ```ignore
/// #[pallet::pallet]
/// #[pallet::generate_storage_info]
/// pub struct Pallet<T>(_);
/// ```
///
/// This requires all storage items to implement the trait `StorageInfoTrait`, thus all keys
/// and value types must be bound by `MaxEncodedLen`. Individual storages can opt-out from this
/// constraint by using [`#[pallet::unbounded]`](`macro@unbounded`) (see
/// [`#[pallet::storage]`](`macro@storage`) for more info).
#[proc_macro_attribute]
pub fn generate_storage_info(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// Because the `pallet::pallet` macro implements `GetStorageVersion`, the current storage
/// version needs to be communicated to the macro. This can be done by using the
/// `pallet::storage_version` attribute:
///
/// ```ignore
/// const STORAGE_VERSION: StorageVersion = StorageVersion::new(5);
///
/// #[pallet::pallet]
/// #[pallet::storage_version(STORAGE_VERSION)]
/// pub struct Pallet<T>(_);
/// ```
///
/// If not present, the current storage version is set to the default value.
#[proc_macro_attribute]
pub fn storage_version(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::hooks]` attribute allows you to specify a `Hooks` implementation for
/// `Pallet` that specifies pallet-specific logic.
///
/// The item the attribute attaches to must be defined as follows:
/// ```ignore
/// #[pallet::hooks]
/// impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> $optional_where_clause {
///     ...
/// }
/// ```
/// I.e. a regular trait implementation with generic bound: `T: Config`, for the trait
/// `Hooks<BlockNumberFor<T>>` (they are defined in preludes), for the type `Pallet<T>` and
/// with an optional where clause.
///
/// If no `#[pallet::hooks]` exists, then the following default implementation is
/// automatically generated:
/// ```ignore
/// #[pallet::hooks]
/// impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {}
/// ```
///
/// ## Macro expansion
///
/// The macro implements the traits `OnInitialize`, `OnIdle`, `OnFinalize`, `OnRuntimeUpgrade`,
/// `OffchainWorker`, and `IntegrityTest` using the provided `Hooks` implementation.
///
/// NOTE: `OnRuntimeUpgrade` is implemented with `Hooks::on_runtime_upgrade` and some
/// additional logic. E.g. logic to write the pallet version into storage.
///
/// NOTE: The macro also adds some tracing logic when implementing the above traits. The
/// following hooks emit traces: `on_initialize`, `on_finalize` and `on_runtime_upgrade`.
#[proc_macro_attribute]
pub fn hooks(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// Each dispatchable needs to define a weight with `#[pallet::weight($expr)]` attribute, the
/// first argument must be `origin: OriginFor<T>`.
#[proc_macro_attribute]
pub fn weight(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// Compact encoding for arguments can be achieved via `#[pallet::compact]`. The function must
/// return a `DispatchResultWithPostInfo` or `DispatchResult`.
#[proc_macro_attribute]
pub fn compact(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// Each dispatchable may also be annotated with the `#[pallet::call_index($idx)]` attribute,
/// which explicitly defines the codec index for the dispatchable function in the `Call` enum.
///
/// All call indexes start from 0, until it encounters a dispatchable function with a defined
/// call index. The dispatchable function that lexically follows the function with a defined
/// call index will have that call index, but incremented by 1, e.g. if there are 3
/// dispatchable functions `fn foo`, `fn bar` and `fn qux` in that order, and only `fn bar`
/// has a call index of 10, then `fn qux` will have an index of 11, instead of 1.
///
/// All arguments must implement [`Debug`], [`PartialEq`], [`Eq`], `Decode`, `Encode`, and
/// [`Clone`]. For ease of use, bound by the trait `frame_support::pallet_prelude::Member`.
///
/// If no `#[pallet::call]` exists, then a default implementation corresponding to the
/// following code is automatically generated:
///
/// ```ignore
/// #[pallet::call]
/// impl<T: Config> Pallet<T> {}
/// ```
///
/// **WARNING**: modifying dispatchables, changing their order, removing some, etc., must be
/// done with care. Indeed this will change the outer runtime call type (which is an enum with
/// one variant per pallet), this outer runtime call can be stored on-chain (e.g. in
/// `pallet-scheduler`). Thus migration might be needed. To mitigate against some of this, the
/// `#[pallet::call_index($idx)]` attribute can be used to fix the order of the dispatchable so
/// that the `Call` enum encoding does not change after modification. As a general rule of
/// thumb, it is therefore adventageous to always add new calls to the end so you can maintain
/// the existing order of calls.
///
/// ### Macro expansion
///
/// The macro creates an enum `Call` with one variant per dispatchable. This enum implements:
/// [`Clone`], [`Eq`], [`PartialEq`], [`Debug`] (with stripped implementation in `not("std")`),
/// `Encode`, `Decode`, `GetDispatchInfo`, `GetCallName`, and `UnfilteredDispatchable`.
///
/// The macro implements the `Callable` trait on `Pallet` and a function `call_functions`
/// which returns the dispatchable metadata.
#[proc_macro_attribute]
pub fn call_index(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// Allows you to define some extra constants to be added into constant metadata.
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::extra_constants]
/// impl<T: Config> Pallet<T> where $optional_where_clause {
/// 	/// $some_doc
/// 	$vis fn $fn_name() -> $some_return_type {
/// 		...
/// 	}
/// 	...
/// }
/// ```
/// I.e. a regular rust `impl` block with some optional where clause and functions with 0 args,
/// 0 generics, and some return type.
///
/// ## Macro expansion
///
/// The macro add some extra constants to pallet constant metadata.
#[proc_macro_attribute]
pub fn extra_constants(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::error]` attribute allows you to define an error enum that will be returned
/// from the dispatchable when an error occurs. The information for this error type is then
/// stored in metadata.
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::error]
/// pub enum Error<T> {
/// 	/// $some_optional_doc
/// 	$SomeFieldLessVariant,
/// 	/// $some_more_optional_doc
/// 	$SomeVariantWithOneField(FieldType),
/// 	...
/// }
/// ```
/// I.e. a regular enum named `Error`, with generic `T` and fieldless or multiple-field
/// variants.
///
/// Any field type in the enum variants must implement `TypeInfo` in order to be properly used
/// in the metadata, and its encoded size should be as small as possible, preferably 1 byte in
/// size in order to reduce storage size. The error enum itself has an absolute maximum encoded
/// size specified by `MAX_MODULE_ERROR_ENCODED_SIZE`.
///
/// (1 byte can still be 256 different errors. The more specific the error, the easier it is to
/// diagnose problems and give a better experience to the user. Don't skimp on having lots of
/// individual error conditions.)
///
/// Field types in enum variants must also implement `PalletError`, otherwise the pallet will
/// fail to compile. Rust primitive types have already implemented the `PalletError` trait
/// along with some commonly used stdlib types such as [`Option`] and `PhantomData`, and hence
/// in most use cases, a manual implementation is not necessary and is discouraged.
///
/// The generic `T` must not bound anything and a `where` clause is not allowed. That said,
/// bounds and/or a where clause should not needed for any use-case.
///
/// ## Macro expansion
///
/// The macro implements the [`Debug`] trait and functions `as_u8` using variant position, and
/// `as_str` using variant doc.
///
/// The macro also implements `From<Error<T>>` for `&'static str` and `From<Error<T>>` for
/// `DispatchError`.
#[proc_macro_attribute]
pub fn error(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::event]` attribute allows you to define pallet events. Pallet events are
/// stored under the `system` / `events` key when the block is applied (and then replaced when
/// the next block writes it's events).
///
/// The Event enum must be defined as follows:
///
/// ```ignore
/// #[pallet::event]
/// #[pallet::generate_deposit($visibility fn deposit_event)] // Optional
/// pub enum Event<$some_generic> $optional_where_clause {
/// 	/// Some doc
/// 	$SomeName($SomeType, $YetanotherType, ...),
/// 	...
/// }
/// ```
///
/// I.e. an enum (with named or unnamed fields variant), named `Event`, with generic: none or
/// `T` or `T: Config`, and optional w here clause.
///
/// Each field must implement [`Clone`], [`Eq`], [`PartialEq`], `Encode`, `Decode`, and
/// [`Debug`] (on std only). For ease of use, bound by the trait `Member`, available in
/// `frame_support::pallet_prelude`.
#[proc_macro_attribute]
pub fn event(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The attribute `#[pallet::generate_deposit($visibility fn deposit_event)]` generates a
/// helper function on `Pallet` that handles deposit events.
///
/// NOTE: For instantiable pallets, the event must be generic over `T` and `I`.
///
/// ## Macro expansion
///
/// The macro will add on enum `Event` the attributes:
/// * `#[derive(frame_support::CloneNoBound)]`
/// * `#[derive(frame_support::EqNoBound)]`
/// * `#[derive(frame_support::PartialEqNoBound)]`
/// * `#[derive(frame_support::RuntimeDebugNoBound)]`
/// * `#[derive(codec::Encode)]`
/// * `#[derive(codec::Decode)]`
///
/// The macro implements `From<Event<..>>` for ().
///
/// The macro implements a metadata function on `Event` returning the `EventMetadata`.
///
/// If `#[pallet::generate_deposit]` is present then the macro implements `fn deposit_event` on
/// `Pallet`.
#[proc_macro_attribute]
pub fn generate_deposit(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::storage]` attribute lets you define some abstract storage inside of runtime
/// storage and also set its metadata. This attribute can be used multiple times.
///
/// Item should be defined as:
///
/// ```ignore
/// #[pallet::storage]
/// #[pallet::getter(fn $getter_name)] // optional
/// $vis type $StorageName<$some_generic> $optional_where_clause
/// 	= $StorageType<$generic_name = $some_generics, $other_name = $some_other, ...>;
/// ```
///
/// or with unnamed generic:
///
/// ```ignore
/// #[pallet::storage]
/// #[pallet::getter(fn $getter_name)] // optional
/// $vis type $StorageName<$some_generic> $optional_where_clause
/// 	= $StorageType<_, $some_generics, ...>;
/// ```
///
/// I.e. it must be a type alias, with generics: `T` or `T: Config`. The aliased type must be
/// one of `StorageValue`, `StorageMap` or `StorageDoubleMap`. The generic arguments of the
/// storage type can be given in two manners: named and unnamed. For named generic arguments,
/// the name for each argument should match the name defined for it on the storage struct:
/// * `StorageValue` expects `Value` and optionally `QueryKind` and `OnEmpty`,
/// * `StorageMap` expects `Hasher`, `Key`, `Value` and optionally `QueryKind` and `OnEmpty`,
/// * `CountedStorageMap` expects `Hasher`, `Key`, `Value` and optionally `QueryKind` and `OnEmpty`,
/// * `StorageDoubleMap` expects `Hasher1`, `Key1`, `Hasher2`, `Key2`, `Value` and optionally
///   `QueryKind` and `OnEmpty`.
///
/// For unnamed generic arguments: Their first generic must be `_` as it is replaced by the
/// macro and other generic must declared as a normal generic type declaration.
///
/// The `Prefix` generic written by the macro is generated using
/// `PalletInfo::name::<Pallet<..>>()` and the name of the storage type. E.g. if runtime names
/// the pallet "MyExample" then the storage `type Foo<T> = ...` should use the prefix:
/// `Twox128(b"MyExample") ++ Twox128(b"Foo")`.
///
/// For the `CountedStorageMap` variant, the `Prefix` also implements
/// `CountedStorageMapInstance`. It also associates a `CounterPrefix`, which is implemented the
/// same as above, but the storage prefix is prepend with `"CounterFor"`. E.g. if runtime names
/// the pallet "MyExample" then the storage `type Foo<T> = CountedStorageaMap<...>` will store
/// its counter at the prefix: `Twox128(b"MyExample") ++ Twox128(b"CounterForFoo")`.
///
/// E.g:
///
/// ```ignore
/// #[pallet::storage]
/// pub(super) type MyStorage<T> = StorageMap<Hasher = Blake2_128Concat, Key = u32, Value = u32>;
/// ```
///
/// In this case the final prefix used by the map is `Twox128(b"MyExample") ++
/// Twox128(b"OtherName")`.
#[proc_macro_attribute]
pub fn storage(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The optional attribute `#[pallet::getter(fn $my_getter_fn_name)]` allows you to define a
/// getter function on `Pallet`.
///
/// Also see [`pallet::storage`](`macro@storage`)
#[proc_macro_attribute]
pub fn getter(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The optional attribute `#[pallet::storage_prefix = "SomeName"]` allows you to define the
/// storage prefix to use. This is helpful if you wish to rename the storage field but don't
/// want to perform a migration.
///
/// E.g:
///
/// ```ignore
/// #[pallet::storage]
/// #[pallet::storage_prefix = "foo"]
/// #[pallet::getter(fn my_storage)]
/// pub(super) type MyStorage<T> = StorageMap<Hasher = Blake2_128Concat, Key = u32, Value = u32>;
/// ```
///
/// or
///
/// ```ignore
/// #[pallet::storage]
/// #[pallet::getter(fn my_storage)]
/// pub(super) type MyStorage<T> = StorageMap<_, Blake2_128Concat, u32, u32>;
/// ```
#[proc_macro_attribute]
pub fn storage_prefix(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The optional attribute `#[pallet::unbounded]` declares the storage as unbounded. When
/// implementating the storage info (when `#[pallet::generate_storage_info]` is specified on
/// the pallet struct placeholder), the size of the storage will be declared as unbounded. This
/// can be useful for storage which can never go into PoV (Proof of Validity).
#[proc_macro_attribute]
pub fn unbounded(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The optional attribute `#[pallet::whitelist_storage]` will declare the
/// storage as whitelisted from benchmarking. Doing so will exclude reads of
/// that value's storage key from counting towards weight calculations during
/// benchmarking.
///
/// This attribute should only be attached to storages that are known to be
/// read/used in every block. This will result in a more accurate benchmarking weight.
///
/// ### Example
/// ```ignore
/// #[pallet::storage]
/// #[pallet::whitelist_storage]
/// pub(super) type Number<T: Config> = StorageValue<_, T::BlockNumber, ValueQuery>;
/// ```
///
/// NOTE: As with all `pallet::*` attributes, this one _must_ be written as
/// `#[pallet::whitelist_storage]` and can only be placed inside a `pallet` module in order for
/// it to work properly.
#[proc_macro_attribute]
pub fn whitelist_storage(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::type_value]` attribute lets you define a struct implementing the `Get` trait
/// to ease the use of storage types. This attribute is meant to be used alongside
/// [`#[pallet::storage]`](`macro@storage`) to define a storage's default value. This attribute
/// can be used multiple times.
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::type_value]
/// fn $MyDefaultName<$some_generic>() -> $default_type $optional_where_clause { $expr }
/// ```
///
/// I.e.: a function definition with generics none or `T: Config` and a returned type.
///
/// E.g.:
///
/// ```ignore
/// #[pallet::type_value]
/// fn MyDefault<T: Config>() -> T::Balance { 3.into() }
/// ```
///
/// ## Macro expansion
///
/// The macro renames the function to some internal name, generates a struct with the original
/// name of the function and its generic, and implements `Get<$ReturnType>` by calling the user
/// defined function.
#[proc_macro_attribute]
pub fn type_value(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::genesis_config]` attribute allows you to define the genesis configuration
/// for the pallet.
///
/// Item is defined as either an enum or a struct. It needs to be public and implement the
/// trait `GenesisBuild` with [`#[pallet::genesis_build]`](`macro@genesis_build`). The type
/// generics are constrained to be either none, or `T` or `T: Config`.
///
/// E.g:
///
/// ```ignore
/// #[pallet::genesis_config]
/// pub struct GenesisConfig<T: Config> {
/// 	_myfield: BalanceOf<T>,
/// }
/// ```
#[proc_macro_attribute]
pub fn genesis_config(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::genesis_build]` attribute allows you to define how `genesis_configuration`
/// is built. This takes as input the `GenesisConfig` type (as `self`) and constructs the pallet's
/// initial state.
///
/// The impl must be defined as:
///
/// ```ignore
/// #[pallet::genesis_build]
/// impl<T: Config> GenesisBuild<T> for GenesisConfig<$maybe_generics> {
/// 	fn build(&self) { $expr }
/// }
/// ```
///
/// I.e. a trait implementation with generic `T: Config`, of trait `GenesisBuild<T>` on
/// type `GenesisConfig` with generics none or `T`.
///
/// E.g.:
///
/// ```ignore
/// #[pallet::genesis_build]
/// impl<T: Config> GenesisBuild<T> for GenesisConfig {
/// 	fn build(&self) {}
/// }
/// ```
///
/// ## Macro expansion
///
/// The macro will add the following attribute:
/// * `#[cfg(feature = "std")]`
///
/// The macro will implement `sp_runtime::BuildModuleGenesisStorage` using `()` as a second
/// generic for non-instantiable pallets.
#[proc_macro_attribute]
pub fn genesis_build(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::inherent]` attribute allows the pallet to provide some
/// [inherent](https://docs.substrate.io/fundamentals/transaction-types/#inherent-transactions).
/// An inherent is some piece of data that is inserted by a block authoring node at block
/// creation time and can either be accepted or rejected by validators based on whether the
/// data falls within an acceptable range.
///
/// The most common inherent is the `timestamp` that is inserted into every block. Since there
/// is no way to validate timestamps, validators simply check that the timestamp reported by
/// the block authoring node falls within an acceptable range.
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::inherent]
/// impl<T: Config> ProvideInherent for Pallet<T> {
/// 	// ... regular trait implementation
/// }
/// ```
///
/// I.e. a trait implementation with bound `T: Config`, of trait `ProvideInherent` for type
/// `Pallet<T>`, and some optional where clause.
///
/// ## Macro expansion
///
/// The macro currently makes no use of this information, but it might use this information in
/// the future to give information directly to `construct_runtime`.
#[proc_macro_attribute]
pub fn inherent(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::validate_unsigned]` attribute allows the pallet to validate some unsigned
/// transaction:
///
/// Item must be defined as:
///
/// ```ignore
/// #[pallet::validate_unsigned]
/// impl<T: Config> ValidateUnsigned for Pallet<T> {
/// 	// ... regular trait implementation
/// }
/// ```
///
/// I.e. a trait implementation with bound `T: Config`, of trait `ValidateUnsigned` for type
/// `Pallet<T>`, and some optional where clause.
///
/// NOTE: There is also the `sp_runtime::traits::SignedExtension` trait that can be used to add
/// some specific logic for transaction validation.
///
/// ## Macro expansion
///
/// The macro currently makes no use of this information, but it might use this information in
/// the future to give information directly to `construct_runtime`.
#[proc_macro_attribute]
pub fn validate_unsigned(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}

/// The `#[pallet::origin]` attribute allows you to define some origin for the pallet.
///
/// Item must be either a type alias, an enum, or a struct. It needs to be public.
///
/// E.g.:
///
/// ```ignore
/// #[pallet::origin]
/// pub struct Origin<T>(PhantomData<(T)>);
/// ```
///
/// **WARNING**: modifying origin changes the outer runtime origin. This outer runtime origin
/// can be stored on-chain (e.g. in `pallet-scheduler`), thus any change must be done with care
/// as it might require some migration.
///
/// NOTE: for instantiable pallets, the origin must be generic over `T` and `I`.
#[proc_macro_attribute]
pub fn origin(_: TokenStream, _: TokenStream) -> TokenStream {
	pallet_macro_stub()
}
