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

#![recursion_limit="256"]

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
///
/// Basic storage consists of a name and a type; supported types are:
///
/// * Value: `Foo: type`: Implements [StorageValue](../srml_support/storage/trait.StorageValue.html).
/// * Map: `Foo: map hasher($hash) type => type`: Implements [StorageMap](../srml_support/storage/trait.StorageMap.html)
///   with `$hash` representing a choice of hashing algorithms available in the
///   [`Hashable` trait](../srml_support/trait.Hashable.html).
///
///   `hasher($hash)` is optional and its default is `blake2_256`.
///
///   /!\ Be careful with each key in the map that is inserted in the trie `$hash(module_name ++ " " ++ storage_name ++ encoding(key))`.
///   If the keys are not trusted (e.g. can be set by a user), a cryptographic `hasher` such as
///   `blake2_256` must be used. Otherwise, other values in storage can be compromised.
///
/// * Linked map: `Foo: linked_map hasher($hash) type => type`: Same as `Map` but also implements
///   [EnumarableStorageMap](../srml_support/storage/trait.EnumerableStorageMap.html).
///
/// * Double map: `Foo: double_map hasher($hash) u32, $hash2(u32) => u32`: Implements `StorageDoubleMap` with
///   `$hash` and `$hash2` representing choices of hashing algorithms available in the
///   [`Hashable` trait](../srml_support/trait.Hashable.html).
///
///   `hasher($hash)` is optional and its default is `blake2_256`.
///
///   /!\ Be careful with each key pair in the double map that is inserted in the trie.
///   The final key is calculated as follows:
///
///   ```nocompile
///   $hash(module_name ++ " " ++ storage_name ++ encoding(first_key)) ++ $hash2(encoding(second_key))
///   ```
///
///   If the first key is untrusted, a cryptographic `hasher` such as `blake2_256` must be used.
///   Otherwise, other values of all storage items can be compromised.
///
///   If the second key is untrusted, a cryptographic `hasher` such as `blake2_256` must be used.
///   Otherwise, other items in storage with the same first key can be compromised.
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
/// * The structure: `Foo::<T>`
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
///			build(|_: &mut StorageOverlay, _: &mut ChildrenStorageOverlay, _: &GenesisConfig<T>| {
///				// Modification of storage
///			})
///		}
/// }
/// ```
///
/// This struct can be exposed as `Config` by the `decl_runtime!` macro.
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
/// Then the genesis config is generated with two generic parameters (i.e. `GenesisConfig<T, I>`)
/// and storage items are accessible using two generic parameters, e.g.:
/// `<Dummy<T, I>>::get()` or `Dummy::<T, I>::get()`.
#[proc_macro]
pub fn decl_storage(input: TokenStream) -> TokenStream {
	storage::transformation::decl_storage_impl(input)
}
