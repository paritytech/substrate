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

use crate::storage::transformation::{DeclStorageTypeInfos, InstanceOpts};

use srml_support_procedural_tools::syn_ext as ext;
use proc_macro2::TokenStream as TokenStream2;
use syn::Ident;
use quote::quote;

pub fn option_unwrap(is_option: bool) -> TokenStream2 {
	if !is_option {
		// raw type case
		quote!( unwrap_or_else )
	} else {
		// Option<> type case
		quote!( or_else )
	}
}

// prefix for consts in trait Instance
pub(crate) const PREFIX_FOR: &str = "PREFIX_FOR_";
pub(crate) const HEAD_KEY_FOR: &str = "HEAD_KEY_FOR_";

pub(crate) struct Impls<'a, I: Iterator<Item=syn::Meta>> {
	pub scrate: &'a TokenStream2,
	pub visibility: &'a syn::Visibility,
	pub traitinstance: &'a syn::Ident,
	pub traittype: &'a syn::TypeParamBound,
	pub instance_opts: &'a InstanceOpts,
	pub type_infos: DeclStorageTypeInfos<'a>,
	pub fielddefault: TokenStream2,
	pub prefix: String,
	pub cratename: &'a syn::Ident,
	pub name: &'a syn::Ident,
	pub attrs: I,
	pub where_clause: &'a Option<syn::WhereClause>,
}

impl<'a, I: Iterator<Item=syn::Meta>> Impls<'a, I> {
	pub fn simple_value(self) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);

		let mutate_impl = if !is_option {
			quote!{
				<Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::put(&val, storage)
			}
		} else {
			quote!{
				match val {
					Some(ref val) => <Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::put(&val, storage),
					None => <Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::kill(storage),
				}
			}
		};

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site());
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if ext::type_contains_ident(
			value_type, traitinstance
		) {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for value
		quote! {
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::hashed::generator::StorageValue<#typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				/// Get the storage key.
				fn key() -> &'static [u8] {
					#final_prefix
				}

				/// Load the value from the provided storage instance.
				fn get<S: #scrate::HashedStorage<#scrate::Twox128>>(storage: &S) -> Self::Query {
					storage.get(<Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::key())
						.#option_simple_1(|| #fielddefault)
				}

				/// Take a value from storage, removing it afterwards.
				fn take<S: #scrate::HashedStorage<#scrate::Twox128>>(storage: &mut S) -> Self::Query {
					storage.take(<Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::key())
						.#option_simple_1(|| #fielddefault)
				}

				/// Mutate the value under a key.
				fn mutate<R, F, S>(f: F, storage: &mut S) -> R
				where
					F: FnOnce(&mut Self::Query) -> R,
					S: #scrate::HashedStorage<#scrate::Twox128>,
				{
					let mut val = <Self as #scrate::storage::hashed::generator::StorageValue<#typ>>::get(storage);

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}
		}
	}

	pub fn map(self, hasher: TokenStream2, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;
		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);

		let as_map = quote!{ <Self as #scrate::storage::hashed::generator::StorageMap<#kty, #typ>> };

		let mutate_impl = if !is_option {
			quote!{
				#as_map::insert(key, &val, storage)
			}
		} else {
			quote!{
				match val {
					Some(ref val) => #as_map::insert(key, &val, storage),
					None => #as_map::remove(key, storage),
				}
			}
		};

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = syn::Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()),
				proc_macro2::Span::call_site(),
			);
			quote! { #instance::#const_name.as_bytes() }
		} else {
			quote! { #prefix.as_bytes() }
		};

		let trait_required = ext::type_contains_ident(value_type, traitinstance)
			|| ext::type_contains_ident(kty, traitinstance);

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if trait_required {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for map
		quote!{
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(
				#scrate::rstd::marker::PhantomData<(#trait_and_instance)>
			) #where_clause;

			impl<#impl_trait> #scrate::storage::hashed::generator::StorageMap<#kty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				type Hasher = #scrate::#hasher;

				/// Get the prefix key in storage.
				fn prefix() -> &'static [u8] {
					#final_prefix
				}

				/// Get the storage key used to fetch a value corresponding to a specific key.
				fn key_for(x: &#kty) -> #scrate::rstd::vec::Vec<u8> {
					let mut key = #as_map::prefix().to_vec();
					#scrate::codec::Encode::encode_to(x, &mut key);
					key
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::HashedStorage<#scrate::#hasher>>(key: &#kty, storage: &S) -> Self::Query {
					let key = #as_map::key_for(key);
					storage.get(&key[..]).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::HashedStorage<#scrate::#hasher>>(key: &#kty, storage: &mut S) -> Self::Query {
					let key = #as_map::key_for(key);
					storage.take(&key[..]).#option_simple_1(|| #fielddefault)
				}

				/// Mutate the value under a key
				fn mutate<R, F, S>(key: &#kty, f: F, storage: &mut S) -> R
				where
					F: FnOnce(&mut Self::Query) -> R,
					S: #scrate::HashedStorage<#scrate::#hasher>,
				{
					let mut val = #as_map::get(key, storage);

					let ret = f(&mut val);
					#mutate_impl ;
					ret
				}
			}

			impl<#impl_trait> #scrate::storage::hashed::generator::AppendableStorageMap<#kty, #typ>
				for #name<#trait_and_instance> #where_clause
			{}
		}
	}

	pub fn linked_map(self, hasher: TokenStream2, kty: &syn::Type) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			instance_opts,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			where_clause,
			..
		} = self;

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		// make sure to use different prefix for head and elements.
		let final_head_key = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", HEAD_KEY_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			let final_head_key = format!("head of {}", prefix);
			quote!{ #final_head_key.as_bytes() }
		};

		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);
		let name_lowercase = name.to_string().to_lowercase();
		let inner_module = Ident::new(
			&format!("__linked_map_details_for_{}_do_not_use", name_lowercase), name.span()
		);
		let linkage = Ident::new(&format!("__LinkageFor{}DoNotUse", name), name.span());
		let phantom_data = quote! { #scrate::rstd::marker::PhantomData };
		let as_map = quote!{ <Self as #scrate::storage::hashed::generator::StorageMap<#kty, #typ>> };
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

		let mutate_map = if type_infos.is_option {
			quote! { .map(|(data, linkage)| (Some(data), Some(linkage))) }
		} else {
			quote! { .map(|(data, linkage)| (data, Some(linkage))) }
		};

		let trait_required = ext::type_contains_ident(value_type, traitinstance)
			|| ext::type_contains_ident(kty, traitinstance);

		let (struct_trait, impl_trait, trait_and_instance) = if trait_required {
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
			)
		};

		let (where_clause, trait_where_clause) = if trait_required {
			(
				where_clause.clone(),
				where_clause.clone().map(|mut wc| {
					wc.predicates.push(syn::parse_quote!(#traitinstance: 'static));
					wc
				}).or_else(|| syn::parse_quote!(where #traitinstance: 'static)),
			)
		} else {
			(
				None,
				None,
			)
		};

		// generator for linked map
		let helpers = quote! {
			/// Linkage data of an element (it's successor and predecessor)
			#[derive(#scrate::codec::Encode, #scrate::codec::Decode)]
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

				impl<'a, S: #scrate::HashedStorage<#scrate::#hasher>, #impl_trait> Iterator
					for Enumerator<'a, S, #kty, (#typ, #trait_and_instance)> #where_clause
				{
					type Item = (#kty, #typ);

					fn next(&mut self) -> Option<Self::Item> {
						let next = self.next.take()?;
						let key_for = <super::#name<#trait_and_instance>
							as #scrate::storage::hashed::generator::StorageMap<#kty, #typ>>::key_for(&next);

						let (val, linkage): (#typ, Linkage<#kty>) = self.storage.get(&*key_for)
							.expect("previous/next only contain existing entires; we enumerate using next; entry exists; qed");
						self.next = linkage.next;
						Some((next, val))
					}
				}

				pub(crate) trait Utils<#struct_trait> {
					/// Update linkage when this element is removed.
					///
					/// Takes care of updating previous and next elements points
					/// as well as updates head if the element is first or last.
					fn remove_linkage<S: #scrate::HashedStorage<#scrate::#hasher>>(linkage: Linkage<#kty>, storage: &mut S);

					/// Read the contained data and it's linkage.
					fn read_with_linkage<S>(storage: &S, key: &[u8]) -> Option<(#typ, Linkage<#kty>)>
					where
						S: #scrate::HashedStorage<#scrate::#hasher>;

					/// Generate linkage for newly inserted element.
					///
					/// Takes care of updating head and previous head's pointer.
					fn new_head_linkage<S: #scrate::HashedStorage<#scrate::#hasher>>(
						storage: &mut S,
						key: &#kty,
					) -> Linkage<#kty>;

					/// Read current head pointer.
					fn read_head<S: #scrate::HashedStorage<#scrate::#hasher>>(storage: &S) -> Option<#kty>;

					/// Overwrite current head pointer.
					///
					/// If `None` is given head is removed from storage.
					fn write_head<S: #scrate::HashedStorage<#scrate::#hasher>>(storage: &mut S, head: Option<&#kty>);
				}
			}
		};

		let structure = quote! {
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>(#phantom_data<(#trait_and_instance)>);

			impl<#impl_trait> self::#inner_module::Utils<#trait_and_instance>
				for #name<#trait_and_instance> #where_clause
			{
				fn remove_linkage<S: #scrate::HashedStorage<#scrate::#hasher>>(
					linkage: self::#inner_module::Linkage<#kty>,
					storage: &mut S,
				) {
					use self::#inner_module::Utils;

					let next_key = linkage.next.as_ref().map(|x| #as_map::key_for(x));
					let prev_key = linkage.previous.as_ref().map(|x| #as_map::key_for(x));

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

				fn read_with_linkage<S: #scrate::HashedStorage<#scrate::#hasher>>(
					storage: &S,
					key: &[u8],
				) -> Option<(#typ, self::#inner_module::Linkage<#kty>)> {
					storage.get(key)
				}

				fn new_head_linkage<S: #scrate::HashedStorage<#scrate::#hasher>>(
					storage: &mut S,
					key: &#kty,
				) -> self::#inner_module::Linkage<#kty> {
					use self::#inner_module::Utils;

					if let Some(head) = Self::read_head(storage) {
						// update previous head predecessor
						{
							let head_key = #as_map::key_for(&head);
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

				fn read_head<S: #scrate::HashedStorage<#scrate::#hasher>>(storage: &S) -> Option<#kty> {
					storage.get(#final_head_key)
				}

				fn write_head<S: #scrate::HashedStorage<#scrate::#hasher>>(storage: &mut S, head: Option<&#kty>) {
					match head {
						Some(head) => storage.put(#final_head_key, head),
						None => storage.kill(#final_head_key),
					}
				}
			}
		};

		quote! {
			#helpers

			#structure

			impl<#impl_trait> #scrate::storage::hashed::generator::StorageMap<#kty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				type Hasher = #scrate::#hasher;

				/// Get the prefix key in storage.
				fn prefix() -> &'static [u8] {
					#final_prefix
				}

				/// Get the storage key used to fetch a value corresponding to a specific key.
				fn key_for(key: &#kty) -> #scrate::rstd::vec::Vec<u8> {
					let mut key_for = #as_map::prefix().to_vec();
					#scrate::codec::Encode::encode_to(&key, &mut key_for);
					key_for
				}

				/// Load the value associated with the given key from the map.
				fn get<S: #scrate::HashedStorage<#scrate::#hasher>>(key: &#kty, storage: &S) -> Self::Query {
					storage.get(&*#as_map::key_for(key)).#option_simple_1(|| #fielddefault)
				}

				/// Take the value, reading and removing it.
				fn take<S: #scrate::HashedStorage<#scrate::#hasher>>(key: &#kty, storage: &mut S) -> Self::Query {
					use self::#inner_module::Utils;

					let res: Option<(#typ, self::#inner_module::Linkage<#kty>)> = storage.take(&*#as_map::key_for(key));

					res.map(|(d, l)| {
						Self::remove_linkage(l, storage);
						d
					}).#option_simple_1(|| #fielddefault)
				}

				/// Remove the value under a key.
				fn remove<S: #scrate::HashedStorage<#scrate::#hasher>>(key: &#kty, storage: &mut S) {
					#as_map::take(key, storage);
				}

				/// Store a value to be associated with the given key from the map.
				fn insert<S: #scrate::HashedStorage<#scrate::#hasher>>(
					key: &#kty,
					val: &#typ,
					storage: &mut S,
				) {
					use self::#inner_module::Utils;

					let key_for = &*#as_map::key_for(key);
					let linkage = match Self::read_with_linkage(storage, key_for) {
						// overwrite but reuse existing linkage
						Some((_data, linkage)) => linkage,
						// create new linkage
						None => Self::new_head_linkage(storage, key),
					};

					storage.put(key_for, &(val, linkage))
				}

				/// Store a value under this key into the provided storage instance; this can take any reference
				/// type that derefs to `T` (and has `Encode` implemented).
				/// Store a value under this key into the provided storage instance.
				fn insert_ref<Arg, S>(key: &#kty, val: &Arg, storage: &mut S)
				where
					#typ: AsRef<Arg>,
					Arg: ?Sized + #scrate::codec::Encode,
					S: #scrate::HashedStorage<#scrate::#hasher>
				{
					use self::#inner_module::Utils;

					let key_for = &*#as_map::key_for(key);
					let linkage = match Self::read_with_linkage(storage, key_for) {
						// overwrite but reuse existing linkage
						Some((_data, linkage)) => linkage,
						// create new linkage
						None => Self::new_head_linkage(storage, key),
					};

					storage.put(key_for, &(val, linkage))
				}

				/// Mutate the value under a key
				fn mutate<R, F, S>(key: &#kty, f: F, storage: &mut S) -> R
				where
					F: FnOnce(&mut Self::Query) -> R,
					S: #scrate::HashedStorage<#scrate::#hasher>,
				{
					use self::#inner_module::Utils;

					let key_for = &*#as_map::key_for(key);
					let (mut val, linkage) = Self::read_with_linkage(storage, key_for)
						#mutate_map
						.unwrap_or_else(|| (#fielddefault, None));

					let ret = f(&mut val);
					#mutate_impl;
					ret
				}
			}

			impl<#impl_trait> #scrate::storage::hashed::generator::EnumerableStorageMap<#kty, #typ>
				for #name<#trait_and_instance> #trait_where_clause
			{
				fn head<S: #scrate::HashedStorage<#scrate::#hasher>>(storage: &S) -> Option<#kty> {
					use self::#inner_module::Utils;

					Self::read_head(storage)
				}

				fn enumerate<'a, S>(
					storage: &'a S
				) -> #scrate::rstd::boxed::Box<dyn Iterator<Item = (#kty, #typ)> + 'a>
					where
						S: #scrate::HashedStorage<#scrate::#hasher>,
						#kty: 'a,
						#typ: 'a,
				{
					use self::#inner_module::{Utils, Enumerator};

					#scrate::rstd::boxed::Box::new(Enumerator {
						next: Self::read_head(storage),
						storage,
						_data: #phantom_data::<(#typ, #trait_and_instance)>::default(),
					})
				}
			}
		}
	}

	pub fn double_map(
		self,
		hasher: TokenStream2,
		k1ty: &syn::Type,
		k2ty: &syn::Type,
		k2_hasher: TokenStream2,
	) -> TokenStream2 {
		let Self {
			scrate,
			visibility,
			traitinstance,
			traittype,
			type_infos,
			fielddefault,
			prefix,
			name,
			attrs,
			instance_opts,
			where_clause,
			..
		} = self;

		let DeclStorageTypeInfos { typ, value_type, is_option, .. } = type_infos;
		let option_simple_1 = option_unwrap(is_option);

		let as_double_map = quote!{
			<Self as #scrate::storage::unhashed::generator::StorageDoubleMap<#k1ty, #k2ty, #typ>>
		};

		let mutate_impl = if !is_option {
			quote!{
				#as_double_map::insert(k1, k2, &val, storage)
			}
		} else {
			quote!{
				match val {
					Some(ref val) => #as_double_map::insert::<KArg1, KArg2, #typ, S>(
						k1,
						k2,
						val,
						storage,
					),
					None => #as_double_map::remove(k1, k2, storage),
				}
			}
		};

		let InstanceOpts {
			equal_default_instance,
			bound_instantiable,
			instance,
			..
		} = instance_opts;

		let final_prefix = if let Some(instance) = instance {
			let const_name = Ident::new(
				&format!("{}{}", PREFIX_FOR, name.to_string()), proc_macro2::Span::call_site()
			);
			quote!{ #instance::#const_name.as_bytes() }
		} else {
			quote!{ #prefix.as_bytes() }
		};

		let (struct_trait, impl_trait, trait_and_instance, where_clause) = if ext::type_contains_ident(
			value_type, traitinstance
		) || ext::type_contains_ident(k1ty, traitinstance) || ext::type_contains_ident(k2ty, traitinstance)
		{
			(
				quote!(#traitinstance: #traittype, #instance #bound_instantiable #equal_default_instance),
				quote!(#traitinstance: #traittype, #instance #bound_instantiable),
				quote!(#traitinstance, #instance),
				where_clause.clone(),
			)
		} else {
			(
				quote!(#instance #bound_instantiable #equal_default_instance),
				quote!(#instance #bound_instantiable),
				quote!(#instance),
				None,
			)
		};

		// generator for double map
		quote!{
			#( #[ #attrs ] )*
			#visibility struct #name<#struct_trait>
				(#scrate::rstd::marker::PhantomData<(#trait_and_instance)>);

			impl<#impl_trait> #scrate::storage::unhashed::generator::StorageDoubleMap<#k1ty, #k2ty, #typ>
				for #name<#trait_and_instance> #where_clause
			{
				type Query = #value_type;

				fn prefix_for<KArg1>(k1: &KArg1) -> #scrate::rstd::vec::Vec<u8> where
					KArg1: ?Sized + #scrate::codec::Encode,
					#k1ty: #scrate::rstd::borrow::Borrow<KArg1>,
				{
					use #scrate::storage::hashed::generator::StorageHasher;

					let mut key = #as_double_map::prefix().to_vec();
					#scrate::codec::Encode::encode_to(k1, &mut key);
					#scrate::#hasher::hash(&key[..]).to_vec()
				}

				fn prefix() -> &'static [u8] {
					#final_prefix
				}

				fn key_for<KArg1, KArg2>(
					k1: &KArg1,
					k2: &KArg2,
				) -> #scrate::rstd::vec::Vec<u8> where
					#k1ty: #scrate::rstd::borrow::Borrow<KArg1>,
					#k2ty: #scrate::rstd::borrow::Borrow<KArg2>,
					KArg1: ?Sized + #scrate::codec::Encode,
					KArg2: ?Sized + #scrate::codec::Encode,
				{
					use #scrate::storage::hashed::generator::StorageHasher;

					let mut key = #as_double_map::prefix_for(k1);
					#scrate::codec::Encode::using_encoded(k2, |e| key.extend(&#scrate::#k2_hasher::hash(e)));
					key
				}

				fn get<KArg1, KArg2, S: #scrate::UnhashedStorage>(
					k1: &KArg1,
					k2: &KArg2,
					storage: &S,
				) -> Self::Query where
					#k1ty: #scrate::rstd::borrow::Borrow<KArg1>,
					#k2ty: #scrate::rstd::borrow::Borrow<KArg2>,
					KArg1: ?Sized + #scrate::codec::Encode,
					KArg2: ?Sized + #scrate::codec::Encode,
				{
					let key = #as_double_map::key_for(k1, k2);
					storage.get(&key).#option_simple_1(|| #fielddefault)
				}

				fn take<KArg1, KArg2, S: #scrate::UnhashedStorage>(
					k1: &KArg1,
					k2: &KArg2,
					storage: &mut S,
				) -> Self::Query where
					#k1ty: #scrate::rstd::borrow::Borrow<KArg1>,
					#k2ty: #scrate::rstd::borrow::Borrow<KArg2>,
					KArg1: ?Sized + #scrate::codec::Encode,
					KArg2: ?Sized + #scrate::codec::Encode,
				{
					let key = #as_double_map::key_for(k1, k2);
					storage.take(&key).#option_simple_1(|| #fielddefault)
				}

				fn mutate<KArg1, KArg2, R, F, S: #scrate::UnhashedStorage>(
					k1: &KArg1,
					k2: &KArg2,
					f: F,
					storage: &mut S,
				) -> R where
					#k1ty: #scrate::rstd::borrow::Borrow<KArg1>,
					#k2ty: #scrate::rstd::borrow::Borrow<KArg2>,
					KArg1: ?Sized + #scrate::codec::Encode,
					KArg2: ?Sized + #scrate::codec::Encode,
					F: FnOnce(&mut Self::Query) -> R,
				{
					let mut val = #as_double_map::get(k1, k2, storage);

					let ret = f(&mut val);
					#mutate_impl;
					ret
				}
			}
		}
	}
}
