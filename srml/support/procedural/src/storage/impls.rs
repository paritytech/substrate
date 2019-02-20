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

use proc_macro2::TokenStream as TokenStream2;
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
					storage.get(<Self as #scrate::storage::generator::StorageValue<#typ>>::key())
						.#option_simple_1(|| #fielddefault)
				}

				/// Take a value from storage, removing it afterwards.
				fn take<S: #scrate::GenericStorage>(storage: &S) -> Self::Query {
					storage.take(<Self as #scrate::storage::generator::StorageValue<#typ>>::key())
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
					let mut key = #prefix.as_bytes().to_vec();
					#scrate::codec::Encode::encode_to(x, &mut key);
					key
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let key = <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
					storage.get(&key[..]).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let key = <Self as #scrate::storage::generator::StorageMap<#kty, #typ>>::key_for(key);
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
		let head_key = format!("head of {}", prefix);
		let prefix = format!("{}", prefix);
		let name_lowercase = name.to_string().to_lowercase();
		let inner_module = syn::Ident::new(&format!("__linked_map_details_for_{}_do_not_use", name_lowercase), name.span());
		let linkage = syn::Ident::new(&format!("__LinkageFor{}DoNotUse", name), name.span());
		let phantom_data = quote! { #scrate::storage::generator::PhantomData };
		let as_map = quote!{ <Self as #scrate::storage::generator::StorageMap<#kty, #typ>> };
		let put_or_insert = quote! {
			match linkage {
				Some(linkage) => storage.put(key_for, &(val, linkage)),
				None => #as_map::insert(key, &val, storage),
			}
		};
		let mutate_impl = if !type_infos.is_option {
			put_or_insert
		} else {
			quote! {
				match val {
					Some(ref val) => #put_or_insert,
					None => #as_map::remove(key, storage),
				}
			}
		};

		// generator for linked map
		let helpers = quote! {
			/// Linkage data of an element (it's successor and predecessor)
			#[derive(#scrate::parity_codec_derive::Encode, #scrate::parity_codec_derive::Decode)]
			pub(crate) struct #linkage<Key> {
				/// Previous element key in storage (None for the first element)
				pub previous: Option<Key>,
				/// Next element key in storage (None for the last element)
				pub next: Option<Key>,
			}

			mod #inner_module {
				use super::*;

				/// Re-exported version of linkage to overcome proc-macro derivation issue.
				pub(crate) use super::#linkage as Linkage;

				impl<Key> Default for Linkage<Key> {
					fn default() -> Self {
						Self {
							previous: None,
							next: None,
						}
					}
				}

				/// A key-value pair iterator for enumerable map.
				pub(crate) struct Enumerator<'a, S, K, V> {
					pub storage: &'a S,
					pub next: Option<K>,
					pub _data: #phantom_data<V>,
				}

				impl<'a, S: #scrate::GenericStorage, K, V> Iterator for Enumerator<'a, S, K, V> where
					K: 'a + #scrate::codec::Codec,
					V: 'a + #scrate::codec::Decode,
				{
					type Item = (K, V);

					fn next(&mut self) -> Option<Self::Item> {
						let next = self.next.take()?;
						let key_for = key_for(&next);
						let (val, linkage): (V, Linkage<K>) = self.storage.get(&*key_for)
							.expect("previous/next only contain existing entires; we enumerate using next; entry exists; qed");
						self.next = linkage.next;
						Some((next, val))
					}
				}

				/// Generate a storage key for given item.
				pub(crate) fn key_for<Key: #scrate::codec::Encode>(key: &Key) -> #scrate::rstd::vec::Vec<u8> {
					let mut key_for = #prefix.as_bytes().to_vec();
					#scrate::codec::Encode::encode_to(&key, &mut key_for);
					key_for
				}

				pub(crate) trait Utils<#traitinstance: #traittype> {
					/// Update linkage when this element is removed.
					///
					/// Takes care of updating previous and next elements points
					/// as well as updates head if the element is first or last.
					fn remove_linkage<S: #scrate::GenericStorage>(linkage: Linkage<#kty>, storage: &S);

					/// Read the contained data and it's linkage.
					fn read_with_linkage<S: #scrate::GenericStorage>(storage: &S, key: &[u8]) -> Option<(#value_type, Linkage<#kty>)>;

					/// Generate linkage for newly inserted element.
					///
					/// Takes care of updating head and previous head's pointer.
					fn new_head_linkage<S: #scrate::GenericStorage>(
						storage: &S,
						key: &#kty,
					) -> Linkage<#kty>;

					/// Read current head pointer.
					fn read_head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty>;

					/// Overwrite current head pointer.
					///
					/// If `None` is given head is removed from storage.
					fn write_head<S: #scrate::GenericStorage>(storage: &S, head: Option<&#kty>);
				}
			}
		};

		let structure = quote! {
			#visibility struct #name<#traitinstance: #traittype>(#phantom_data<#traitinstance>);

			impl<#traitinstance: #traittype> self::#inner_module::Utils<#traitinstance> for #name<#traitinstance> {
				fn remove_linkage<S: #scrate::GenericStorage>(
					linkage: self::#inner_module::Linkage<#kty>,
					storage: &S,
				) {
					use self::#inner_module::{key_for, Utils};

					let next_key = linkage.next.as_ref().map(|x| key_for(x));
					let prev_key = linkage.previous.as_ref().map(|x| key_for(x));

					if let Some(prev_key) = prev_key {
						// Retrieve previous element and update `next`
						let mut res = Self::read_with_linkage(storage, &*prev_key)
							.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
						res.1.next = linkage.next;
						storage.put(&*prev_key, &res);
					} else {
						// we were first so let's update the head
						Self::write_head(storage, linkage.next.as_ref());
					}

					if let Some(next_key) = next_key {
						// Update previous of next element
						let mut res = Self::read_with_linkage(storage, &*next_key)
							.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
						res.1.previous = linkage.previous;
						storage.put(&*next_key, &res);
					}
				}

				fn read_with_linkage<S: #scrate::GenericStorage>(
					storage: &S,
					key: &[u8],
				) -> Option<(#value_type, self::#inner_module::Linkage<#kty>)> {
					storage.get(key)
				}

				fn new_head_linkage<S: #scrate::GenericStorage>(
					storage: &S,
					key: &#kty,
				) -> self::#inner_module::Linkage<#kty> {
					use self::#inner_module::{key_for, Utils};

					if let Some(head) = Self::read_head(storage) {
						// update previous head predecessor
						{
							let head_key = key_for(&head);
							let (data, linkage) = Self::read_with_linkage(storage, &*head_key).expect(r#"
								head is set when first element is inserted and unset when last element is removed;
								if head is Some then it points to existing key; qed
							"#);
							storage.put(&*head_key, &(data, self::#inner_module::Linkage {
								next: linkage.next.as_ref(),
								previous: Some(key),
							}));
						}
						// update to current head
						Self::write_head(storage, Some(key));
						// return linkage with pointer to previous head
						let mut linkage = self::#inner_module::Linkage::default();
						linkage.next = Some(head);
						linkage
					} else {
						// we are first - update the head and produce empty linkage
						Self::write_head(storage, Some(key));
						self::#inner_module::Linkage::default()
					}
				}

				fn read_head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty> {
					storage.get(#head_key.as_bytes())
				}

				fn write_head<S: #scrate::GenericStorage>(storage: &S, head: Option<&#kty>) {
					match head {
						Some(head) => storage.put(#head_key.as_bytes(), head),
						None => storage.kill(#head_key.as_bytes()),
					}
				}
			}
		};

		quote! {
			#helpers

			#structure

			impl<#traitinstance: #traittype> #scrate::storage::generator::StorageMap<#kty, #typ> for #name<#traitinstance> {
				type Query = #value_type;

				/// Get the prefix key in storage.
				fn prefix() -> &'static [u8] {
					#prefix.as_bytes()
				}

				/// Get the storage key used to fetch a value corresponding to a specific key.
				fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
					self::#inner_module::key_for(x)
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					storage.get(&*#as_map::key_for(key)).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					use self::#inner_module::{Utils, key_for};

					let res: Option<(#value_type, self::#inner_module::Linkage<#kty>)> = storage.take(&*key_for(key));
					match res {
						Some((data, linkage)) => {
							Self::remove_linkage(linkage, storage);
							data
						},
						None => #fielddefault,
					}
				}

				/// Remove the value under a key.
				fn remove<S: #scrate::GenericStorage>(key: &#kty, storage: &S) {
					#as_map::take(key, storage);
				}

				/// Store a value to be associated with the given key from the map.
				fn insert<S: #scrate::GenericStorage>(key: &#kty, val: &#typ, storage: &S) {
					use self::#inner_module::{Utils, key_for};

					let key_for = &*key_for(key);
					let linkage = match Self::read_with_linkage(storage, key_for) {
						// overwrite but reuse existing linkage
						Some((_data, linkage)) => linkage,
						// create new linkage
						None => Self::new_head_linkage(storage, key),
					};
					storage.put(key_for, &(val, linkage))
				}

				/// Mutate the value under a key
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
					use self::#inner_module::{Utils, key_for};

					let key_for = &*key_for(key);
					let (mut val, linkage) = Self::read_with_linkage(storage, key_for)
						.map(|(data, linkage)| (data, Some(linkage)))
						.unwrap_or_else(|| (#fielddefault, None));

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}

			impl<#traitinstance: #traittype> #scrate::storage::generator::EnumerableStorageMap<#kty, #typ> for #name<#traitinstance> {
				fn head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty> {
					use self::#inner_module::Utils;

					Self::read_head(storage)
				}

				fn enumerate<'a, S: #scrate::GenericStorage>(storage: &'a S) -> #scrate::storage::generator::Box<dyn Iterator<Item = (#kty, #typ)> + 'a> where
					#kty: 'a,
					#typ: 'a,
				{
					use self::#inner_module::{Utils, Enumerator};

					#scrate::storage::generator::Box::new(Enumerator {
						next: Self::read_head(storage),
						storage,
						_data: #phantom_data::<#typ>::default(),
					})
				}
			}
		}
	}
}
