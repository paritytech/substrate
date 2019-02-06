// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use proc_macro2::{TokenStream as TokenStream2};
use storage::transformation::DeclStorageTypeInfos;
use syn;

pub fn option_unwrap(is_option: bool) -> TokenStream2 {
	if !is_option {
		// raw type case
		quote!( unwrap_or_else )
	} else {
		// Option<> type case
		quote!( or_else )
	}
}

pub(crate) struct Impls<'a> {
	pub scrate: &'a TokenStream2,
	pub visibility: &'a syn::Visibility,
	pub traitinstance: &'a syn::Ident,
	pub traittype: &'a syn::TypeParamBound,
	pub type_infos: DeclStorageTypeInfos<'a>,
	pub fielddefault: TokenStream2,
	pub prefix: String,
	pub name: &'a syn::Ident,
}

impl<'a> Impls<'a> {
	pub fn simple_value(self) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault,
			prefix,
			name,
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);

		let mutate_impl = if !is_option {
			quote!{
				<Self as #scrate::storage::generator::StorageValue<#typ>>::put(&val, storage)
			}
		} else {
			quote!{
				match val {
					Some(ref val) => <Self as #scrate::storage::generator::StorageValue<#typ>>::put(&val, storage),
					None => <Self as #scrate::storage::generator::StorageValue<#typ>>::kill(storage),
				}
			}
		};

		// generator for value
		quote!{

			#visibility struct #name<#traitinstance: #traittype>(#scrate::storage::generator::PhantomData<#traitinstance>);

			impl<#traitinstance: #traittype> #scrate::storage::generator::StorageValue<#typ> for #name<#traitinstance> {
				type Query = #value_type;

				/// Get the storage key.
				fn key() -> &'static [u8] {
					#prefix.as_bytes()
				}

				/// Load the value from the provided storage instance.
				fn get<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
					storage.get(<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>>::key())
						.#option_simple_1(|| #fielddefault)
				}

				/// Take a value from storage, removing it afterwards.
				fn take<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
					storage.take(<#name<#traitinstance> as #scrate::storage::generator::StorageValue<#typ>>::key())
						.#option_simple_1(|| #fielddefault)
				}

				/// Mutate the value under a key.
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(f: F, storage: &S) -> R {
					let mut val = <Self as #scrate::storage::generator::StorageValue<#typ>>::get(storage);

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}

		}
	}

	pub fn map(self, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault,
			prefix,
			name,
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);

		let mutate_impl = if !is_option {
			quote!{
				<Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::insert(key, &val, storage)
			}
		} else {
			quote!{
				match val {
					Some(ref val) => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::insert(key, &val, storage),
					None => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::remove(key, storage),
				}
			}
		};
		// generator for map
		quote!{
			#visibility struct #name<#traitinstance: #traittype>(#scrate::storage::generator::PhantomData<#traitinstance>);

			impl<#traitinstance: #traittype> #scrate::storage::generator::StorageMap<#kty, #typ> for #name<#traitinstance> {
				type Query = #value_type;

				/// Get the prefix key in storage.
				fn prefix() -> &'static [u8] {
					#prefix.as_bytes()
				}

				/// Get the storage key used to fetch a value corresponding to a specific key.
				fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
					let mut key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::prefix().to_vec();
					#scrate::codec::Encode::encode_to(x, &mut key);
					key
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
					storage.get(&key[..]).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
					storage.take(&key[..]).#option_simple_1(|| #fielddefault)
				}

				/// Mutate the value under a key
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
					let mut val = <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::get(key, storage);

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}

			}
		}
	}

	pub fn linked_map(self, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault,
			prefix,
			name,
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);
		let (default_linkage, with_linkage, split_linkage) = {
			let default_linkage = quote! { () };
			let with_linkage = quote! { (|a, b| a) };
			let split_linkage = quote! { (|a| (a, ())) };

			(default_linkage, with_linkage, split_linkage)
		};
		let key_for = quote! {
			&(<#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key))[..]
		};
		let mutate_impl = if !type_infos.is_option {
			quote!{
				storage.put(key_for, #with_linkage(&val, linkage));
			}
		} else {
			quote!{
				match val {
					Some(ref val) => storage.put(key_for, #with_linkage(val, linkage)),
					None => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::remove(key, storage),
				}
			}
		};
		// generator for map
		quote!{
			#visibility struct #name<#traitinstance: #traittype>(#scrate::storage::generator::PhantomData<#traitinstance>);

			impl<#traitinstance: #traittype> #scrate::storage::generator::StorageMap<#kty, #typ> for #name<#traitinstance> {
				type Query = #value_type;

				/// Get the prefix key in storage.
				fn prefix() -> &'static [u8] {
					#prefix.as_bytes()
				}

				/// Get the storage key used to fetch a value corresponding to a specific key.
				fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
					let mut key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::prefix().to_vec();
					#scrate::codec::Encode::encode_to(x, &mut key);
					key
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let (data, _linkage) = #split_linkage(storage.get(#key_for));
					data.#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let (data, _linkage) = #split_linkage(storage.take(#key_for));
					// TODO [ToDr] Update linkage
					data.#option_simple_1(|| #fielddefault)
				}

				/// Remove the value under a key.
				fn remove<S: #scrate::GenericStorage>(key: &#kty, storage: &S) {
					// TODO [ToDr] Update linkage
					storage.kill(#key_for);
				}

				/// Store a value to be associated with the given key from the map.
				fn insert<S: #scrate::GenericStorage>(key: &#kty, val: &#typ, storage: &S) {
					// TODO [ToDr] depending if the item exists we should either update or compute new linkage
					// TODO [ToDr] How is it supposed to work with Option<>?
					storage.put(#key_for, #with_linkage(val, #default_linkage));
				}

				/// Mutate the value under a key
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
					let key_for = #key_for;
					let (val, linkage) = #split_linkage(storage.get(key_for));
					let mut val: Self::Query = val.#option_simple_1(|| #fielddefault);

					// TODO [ToDr] Might need to compute new linkage if it's inserted for the first time.
					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}
		}
	}
}
