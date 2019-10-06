// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

// tag::description[]
//! Proc macro of Support code for the runtime.
// end::description[]

#![recursion_limit="512"]

extern crate proc_macro;

mod storage;

use proc_macro::TokenStream;

/// Declares strongly-typed wrappers around codec-compatible types in storage.
///
/// ## Example
///
/// ```nocompile
/// decl_storage! {
/// 	trait Store for Module<T: Trait> as Example {
/// 		Foo get(foo) config(): u32=12;
/// 		Bar: map u32 => u32;
/// 		pub Zed build(|config| vec![(0, 0)]): linked_map u32 => u32;
/// 	}
/// }
/// ```
///
/// Declaration is set with the header `(pub) trait Store for Module<T: Trait> as Example`,
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
///   [`StorageValue`](../srml_support/storage/trait.StorageValue.html) trait using the
///   [`StorageValue generator`](../srml_support/storage/generator/trait.StorageValue.html).
///   The generator `unhashed_key` is `$module_prefix ++ " " ++ $storage_name`
///
/// * Map: `Foo: map hasher($hash) type => type`: Implements the
///   [`StorageMap`](../srml_support/storage/trait.StorageMap.html) trait using the
///   [`StorageMap generator`](../srml_support/storage/generator/trait.StorageMap.html).
///
///   `$hash` representing a choice of hashing algorithms available in the
///   [`Hashable`](../srml_support/trait.Hashable.html) trait.
///
///   `hasher($hash)` is optional and its default is `blake2_256`. One should use another hasher
///   with care, see generator documentation.
///
///   The generator is implemented with:
///   * `prefix`: `$module_prefix ++ " " ++ $storage_name`
///   * `Hasher`: $hash
///
/// * Linked map: `Foo: linked_map hasher($hash) type => type`: Implements the
///   [`StorageLinkedMap`](../srml_support/storage/trait.StorageLinkedMap.html) trait using the
///   [`StorageLinkedMap generator`](../srml_support/storage/generator/trait.StorageLinkedMap.html).
///
///   `$hash` representing a choice of hashing algorithms available in the
///   [`Hashable`](../srml_support/trait.Hashable.html) trait.
///
///   `hasher($hash)` is optional and its default is `blake2_256`. One should use another hasher
///   with care, see generator documentation.
///
///   The generator is implemented with:
///   * `prefix`: `$module_prefix ++ " " ++ $storage_name`
///   * `head_key`: `"head of " ++ $module_prefix ++ " " ++ $storage_name`
///   * `Hasher`: $hash
///
/// * Double map: `Foo: double_map hasher($hash1) u32, $hash2(u32) => u32`: Implements the
///   [`StorageDoubleMap`](../srml_support/storage/trait.StorageDoubleMap.html) trait using the
///   [`StorageDoubleMap generator`](../srml_support/storage/generator/trait.StorageDoubleMap.html).
///
///   `$hash1` and `$hash2` representing choices of hashing algorithms available in the
///   [`Hashable`](../srml_support/trait.Hashable.html) trait. They must be choosen with care, see
///   generator documentation.
///
///   `hasher($hash)` is optional and its default is `blake2_256`.
///
///   `hasher($hash)` is optional and its default is `blake2_256`. One should use another hasher
///   with care, see generator documentation.
///
///   If the first key is untrusted, a cryptographic `hasher` such as `blake2_256` must be used.
///   Otherwise, other values of all storage items can be compromised.
///
///   If the second key is untrusted, a cryptographic `hasher` such as `blake2_256` must be used.
///   Otherwise, other items in storage with the same first key can be compromised.
///
///   The generator is implemented with:
///   * `key1_prefix`: `$module_prefix ++ " " ++ $storage_name`
///   * `Hasher1`: $hash1
///   * `Hasher2`: $hash2
///
/// Supported hashers (ordered from least to best security):
///
/// * `twox_64_concat` - TwoX with 64bit + key concatenated.
/// * `twox_128` - TwoX with 128bit.
/// * `twox_256` - TwoX with with 256bit.
/// * `blake2_128` - Blake2 with 128bit.
/// * `blake2_256` - Blake2 with 256bit.
///
/// Basic storage can be extended as such:
///
/// `#vis #name get(#getter) config(#field_name) build(#closure): #type = #default;`
///
/// * `#vis`: Set the visibility of the structure. `pub` or nothing.
/// * `#name`: Name of the storage item, used as a prefix in storage.
/// * [optional] `get(#getter)`: Implements the function #getter to `Module`.
/// * [optional] `config(#field_name)`: `field_name` is optional if get is set.
/// Will include the item in `GenesisConfig`.
/// * [optional] `build(#closure)`: Closure called with storage overlays.
/// * `#type`: Storage type.
/// * [optional] `#default`: Value returned when none.
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
/// 	trait Store for Module<T: Trait> as Example {
///
/// 		// Your storage items
/// 	}
///		add_extra_genesis {
///			config(genesis_field): GenesisFieldType;
///			config(genesis_field2): GenesisFieldType;
///			...
///			build(|_: &Self| {
///				// Modification of storage
///			})
///		}
/// }
/// ```
///
/// This struct can be exposed as `ExampleConfig` by the `construct_runtime!` macro like follows:
///
/// ```nocompile
/// construct_runtime!(
/// 	pub enum Runtume with ... {
///         ...,
///         Example: example::{Module, Storage, ..., Config<T>},
///         ...,
///	}
/// );
/// ```
///
/// ### Module with Instances
///
/// The `decl_storage!` macro supports building modules with instances with the following syntax
/// (`DefaultInstance` type is optional):
///
/// ```nocompile
/// trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Example {}
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
/// trait Store for Module<T: Trait> as Example where T::AccountId: std::fmt::Display {}
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
/// ...
///
/// This adds a field to your `GenesisConfig` with the name `phantom` that you can initialize with
/// `Default::default()`.
///
#[proc_macro]
pub fn decl_storage(input: TokenStream) -> TokenStream {
	storage::transformation::decl_storage_impl(input)
}
