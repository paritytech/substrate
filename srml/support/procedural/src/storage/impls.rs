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
use syn;
use quote::quote;
use crate::storage::transformation::DeclStorageTypeInfos;

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
		// make sure to use different prefix for head and elements.
		let head_key = format!("{}{}", prefix, "head");
		let prefix = format!("{}{}", prefix, prefix);
		let key_for = quote! {
			&(<#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key))[..]
		};
		let linkage = syn::Ident::new(&format!("Linkage{}", name), name.span());
		let enumerator = syn::Ident::new(&format!("Enumerator{}", name), name.span());
		let put_or_insert = quote! {
			match linkage {
				Some(linkage) => storage.put(key_for, &(val, linkage)),
				None => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::insert(key, &val, storage),
			}
		};
		let mutate_impl = if !type_infos.is_option {
			put_or_insert
		} else {
			quote! {
				match val {
					Some(ref val) => #put_or_insert,
					None => <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::remove(key, storage),
				}
			}
		};

		// generator for linked map
		quote! {
			#[derive(Default, parity_codec_derive::Encode, parity_codec_derive::Decode)]
			struct #linkage {
				/// Previous element key in storage (None for the first element)
				previous: Option<#scrate::rstd::vec::Vec<u8>>,
				/// Next element key in storage (None for the last element)
				next: Option<#scrate::rstd::vec::Vec<u8>>,
			}

			impl #linkage {
				/// Update linkage when this element is removed.
				///
				/// Takes care of updating previous and next elements points
				/// as well as updates head if the element is first or last.
				pub fn remove<S: #scrate::GenericStorage>(&self, storage: &S) {
					if let Some(ref prev) = self.previous {
						// Retrieve previous element and update `next`
						let mut res = Self::read(storage, prev)
							.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
						res.1.next = self.next.clone();
						storage::put(prev, &res);
					} else {
						// we were first so let's update the head
						Self::write_head(storage, self.next.as_ref());
					}

					if let Some(ref next) = self.next {
						// Update previous of next element
						let mut res = Self::read(storage, next)
							.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
						res.1.previous = self.previous.clone();
						storage::put(next, &res);
					}
				}

				/// Read the contained data and it's linkage.
				pub fn read<S: #scrate::GenericStorage>(storage: &S, key: &[u8]) -> Option<(#value_type, #linkage)> {
					storage.get(key)
				}

				/// Generate linkage for newly inserted element.
				///
				/// Takes care of updating head and previous head's pointer.
				pub fn insert_new_head<S: #scrate::GenericStorage>(
					storage: &S,
					key: &#scrate::rstd::vec::Vec<u8>
				) -> Self {
					if let Some(head) = Self::read_head(storage) {
						// update previous head
						{
							let (elem, mut linkage) = #linkage::read(storage, &head).expect(r#"
								head is set when first element is inserted and unset when last element is removed;
								if head is Some then it points to existing key; qed
							"#);
							linkage.previous = Some(key.clone());
							storage.put(&head, &(elem, linkage));
						}
						// update the head and return linkage for inserted element
						Self::write_head(storage, Some(&key));
						let mut linkage = Self::default();
						// point to previous head
						linkage.next = Some(head);
						linkage
					} else {
						// we are first - update the head and produce empty linkage
						Self::write_head(storage, Some(&key));
						Self::default()
					}
				}

				/// Get head's storage key.
				fn head_key() -> #scrate::rstd::vec::Vec<u8> {
					#head_key.as_bytes().to_vec()
				}

				/// Read current head pointer.
				fn read_head<S: #scrate::GenericStorage>(storage: &S) -> Option<#scrate::rstd::vec::Vec<u8>> {
					storage.get(&*Self::head_key())
				}

				/// Overwrite current head pointer.
				///
				/// If `None` is given head is removed from storage.
				fn write_head<S: #scrate::GenericStorage>(storage: &S, head: Option<&#scrate::rstd::vec::Vec<u8>>) {
					match head {
						Some(head) => storage.put(&*Self::head_key(), head),
						None => storage.kill(&*Self::head_key()),
					}
				}
			}

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
					#linkage::read(storage, #key_for)
						.map(|x| x.0)
						.#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let res: Option<(#value_type, #linkage)> = storage.take(#key_for);
					match res {
						Some((data, linkage)) => {
							linkage.remove(storage);
							data
						},
						None => #fielddefault
					}
				}

				/// Remove the value under a key.
				fn remove<S: #scrate::GenericStorage>(key: &#kty, storage: &S) {
					<Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::take(key, storage);
				}

				/// Store a value to be associated with the given key from the map.
				fn insert<S: #scrate::GenericStorage>(key: &#kty, val: &#typ, storage: &S) {
					let key = <#name<#traitinstance> as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
					let key_for = &*key;
					let linkage = match #linkage::read(storage, key_for) {
						// overwrite but reuse existing linkage
						Some((_data, linkage)) => linkage,
						// create new linkage
						None => #linkage::insert_new_head(storage, &key),
					};
					storage.put(key_for, &(*val, linkage))
				}

				/// Mutate the value under a key
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
					let key_for = #key_for;
					let (mut val, linkage) = #linkage::read(storage, key_for)
						.map(|(data, linkage)| (data, Some(linkage)))
						.#option_simple_1(|| (#fielddefault, None));

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}

			pub struct #enumerator;

			impl Iterator for #enumerator {
				type Item = (#kty, #typ);

				fn next(&mut self) -> Option<Self::Item> {
					unimplemented!()
				}
			}

			impl<#traitinstance: #traittype> #scrate::storage::generator::EnumerableStorageMap<#kty, #typ> for #name<#traitinstance> {
				type Enumerate = #enumerator;

				fn head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty> {
					unimplemented!()
				}

				fn enumerate<S: #scrate::GenericStorage>(storage: &S) -> Self::Enumerate {
					unimplemented!()
				}
			}
		}
	}
}
