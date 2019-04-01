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
/// Declaration is set with this header `(pub) trait Store for Module<T: Trait> as Example`
/// with `Store` a (pub) trait generated associating each storage to the Module and
/// `as Example` setting the prefix used for storages of this module, it must be unique,
/// another module with same name and same inner storage name will conflict.
///
/// Basic storage consist of a name and a type, supported types are:
/// * storage value: `Foo: type`: implements [StorageValue](https://crates.parity.io/srml_support/storage/trait.StorageValue.html)
/// * storage map: `Foo: map type => type`: implements [StorageMap](https://crates.parity.io/srml_support/storage/trait.StorageMap.html)
/// * storage linked map: `Foo: linked_map type => type`: implements [StorageMap](https://crates.parity.io/srml_support/storage/trait.StorageMap.html) and [EnumarableStorageMap](https://crates.parity.io/srml_support/storage/trait.EnumerableStorageMap.html)
/// * storage double map: Foo: double_map u32, $hash(u32) => u32;` implements `StorageDoubleMap` with hasher $hash one available in `Hashable` trait
/// /!\ be careful while choosing the Hash, indeed malicious could craft second keys to lower the trie.
///
/// And it can be extended as such:
///
/// `#vis #name get(#getter) config(#field_name) build(#closure): #type = #default;`
/// * `#vis`: set the visibility of the structure
/// * `#name`: name of the storage, used as a prefix in the storage
/// * [optional] `get(#getter)`: implements the function #getter to `Module`
/// * [optional] `config(#field_name)`: `field_name` is optional if get is set: include in `GenesisConfig`
/// * [optional] `build(#closure)`: closure called with storage overlays
/// * `#type`: storage type
/// * [optional] `#default`: value returned when none
///
/// Storages are accessible in multiples ways, using:
/// * the structure: `Foo::<T>`
/// * the `Store` trait structure: `<Module<T> as Store>::Foo`
/// * the getter on the module which calls get on the structure: `Module::<T>::foo()`
///
/// ## GenesisConfig
///
/// An optional `GenesisConfig` struct for storage initialization can be defined, either
/// when at least one storage field requires default initialization
/// (both `get` and `config` or `build`), or specifically as in :
/// ```nocompile
/// decl_storage! {
/// 	trait Store for Module<T: Trait> as Example {
/// 	}
///		add_extra_genesis {
///			config(genesis_field): GenesisFieldType;
///			config(genesis_field2): GenesisFieldType;
///			...
///			build(|_: &mut StorageOverlay, _: &mut ChildrenStorageOverlay, _: &GenesisConfig<T>| {
///				// Modification of storages
///			})
///		}
/// }
/// ```
/// This struct can be expose as `Config` by `decl_runtime` macro.
///
/// ### Module with instances
///
/// `decl_storage!` macro support building modules with instances with the following syntax: (DefaultInstance type
/// is optional)
/// ```nocompile
/// trait Store for Module<T: Trait<I>, I: Instance=DefaultInstance> as Example {}
/// ```
///
/// Then the genesis config is generated with two generic parameter `GenesisConfig<T, I>`
/// and storages are now accessible using two generic parameters like:
/// `<Dummy<T, I>>::get()` or `Dummy::<T, I>::get()`
#[proc_macro]
pub fn decl_storage(input: TokenStream) -> TokenStream {
	storage::transformation::decl_storage_impl(input)
}
