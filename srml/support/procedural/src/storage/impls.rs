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
		let key_for = syn::Ident::new(&format!("key_for_{}", name_lowercase), name.span());
		let internal_module = syn::Ident::new(&format!("__internal_do_not_use_{}", name_lowercase), name.span());
		let linkage = syn::Ident::new(&format!("Linkage{}", name), name.span());
		let borrowing_linkage = syn::Ident::new(&format!("Borrowing{}", linkage), name.span());
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

			mod #internal_module {
				use super::*;

				#[derive(Default, parity_codec_derive::Encode, parity_codec_derive::Decode)]
				pub struct #linkage {
					/// Previous element key in storage (None for the first element)
					previous: Option<#kty>,
					/// Next element key in storage (None for the last element)
					next: Option<#kty>,
				}

				/// A helper struct to avoid unnecessary key cloning.
				///
				/// NOTE It has to have exact same parity-codec encoding as #linkage!
				#[derive(parity_codec_derive::Encode)]
				struct #borrowing_linkage<'a> {
					previous: Option<&'a #kty>,
					next: Option<&'a #kty>,
				}

				impl #linkage {
					/// Update linkage when this element is removed.
					///
					/// Takes care of updating previous and next elements points
					/// as well as updates head if the element is first or last.
					pub fn remove<S: #scrate::GenericStorage>(
						self,
						storage: &S,
					) {
						let next_key = self.next.as_ref().map(|x| #key_for(x));
						let prev_key = self.previous.as_ref().map(|x| #key_for(x));

						if let Some(prev_key) = prev_key {
							// Retrieve previous element and update `next`
							let mut res = Self::read(storage, &*prev_key)
								.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
							res.1.next = self.next;
							storage.put(&*prev_key, &res);
						} else {
							// we were first so let's update the head
							Self::write_head(storage, self.next.as_ref());
						}

						if let Some(next_key) = next_key {
							// Update previous of next element
							let mut res = Self::read(storage, &*next_key)
								.expect("Linkage is updated in case entry is removed; it always points to existing keys; qed");
							res.1.previous = self.previous;
							storage.put(&*next_key, &res);
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
						key: &#kty,
					) -> Self {
						if let Some(head) = Self::read_head(storage) {
							// update previous head predecessor
							{
								let head_key = #key_for(&head);
								let (data, linkage) = Self::read(storage, &*head_key).expect(r#"
									head is set when first element is inserted and unset when last element is removed;
									if head is Some then it points to existing key; qed
								"#);
								storage.put(&*head_key, &(data, #borrowing_linkage {
									next: linkage.next.as_ref(),
									previous: Some(key),
								}));
							}
							// update to current head
							Self::write_head(storage, Some(key));
							// return linkage with pointer to previous head
							let mut linkage = Self::default();
							linkage.next = Some(head);
							linkage
						} else {
							// we are first - update the head and produce empty linkage
							Self::write_head(storage, Some(key));
							Self::default()
						}
					}

					/// Read current head pointer.
					pub fn read_head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty> {
						storage.get(#head_key.as_bytes())
					}

					/// Overwrite current head pointer.
					///
					/// If `None` is given head is removed from storage.
					fn write_head<S: #scrate::GenericStorage>(storage: &S, head: Option<&#kty>) {
						match head {
							Some(head) => storage.put(#head_key.as_bytes(), head),
							None => storage.kill(#head_key.as_bytes()),
						}
					}
				}

				pub struct #enumerator<'a, S> {
					pub storage: &'a S,
					pub next: Option<#kty>,
				}

				impl<'a, S: #scrate::GenericStorage> Iterator for #enumerator<'a, S> {
					type Item = (#kty, #typ);

					fn next(&mut self) -> Option<Self::Item> {
						let next = self.next.take()?;
						let key_for = #key_for(&next);
						let (val, linkage) = #linkage::read(self.storage, &*key_for)
							.expect("previous/next only contain existing entires; we enumerate using next; entry exists; qed");
						self.next = linkage.next;
						Some((next, val))
					}
				}
			}

			fn #key_for(key: &#kty) -> #scrate::rstd::vec::Vec<u8> {
				let mut key_for = #prefix.as_bytes().to_vec();
				#scrate::codec::Encode::encode_to(&key, &mut key_for);
				key_for
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
					#key_for(x)
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					storage.get(&*#key_for(key)).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::GenericStorage>(key: &#kty, storage: &S) -> Self::Query {
					let res: Option<(#value_type, self::#internal_module::#linkage)> = storage.take(&*#key_for(key));
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
					let key_for = &*#key_for(key);
					let linkage = match self::#internal_module::#linkage::read(storage, key_for) {
						// overwrite but reuse existing linkage
						Some((_data, linkage)) => linkage,
						// create new linkage
						None => self::#internal_module::#linkage::insert_new_head(storage, key),
					};
					storage.put(key_for, &(*val, linkage))
				}

				/// Mutate the value under a key
				fn mutate<R, F: FnOnce(&mut Self::Query) -> R, S: #scrate::GenericStorage>(key: &#kty, f: F, storage: &S) -> R {
					let key_for = &*#key_for(key);
					let (mut val, linkage) = self::#internal_module::#linkage::read(storage, key_for)
						.map(|(data, linkage)| (data, Some(linkage)))
						.#option_simple_1(|| (#fielddefault, None));

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}

			impl<#traitinstance: #traittype> #scrate::storage::generator::EnumerableStorageMap<#kty, #typ> for #name<#traitinstance> {
				fn head<S: #scrate::GenericStorage>(storage: &S) -> Option<#kty> {
					self::#internal_module::#linkage::read_head(storage)
				}

				fn enumerate<'a, S: #scrate::GenericStorage>(storage: &'a S) -> #scrate::storage::generator::Box<dyn Iterator<Item = (#kty, #typ)> + 'a> {
					#scrate::storage::generator::Box::new(self::#internal_module::#enumerator {
						next: self::#internal_module::#linkage::read_head(storage),
						storage,
					})
				}
			}
		}
	}
}
