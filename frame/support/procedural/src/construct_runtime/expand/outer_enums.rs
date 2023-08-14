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
// limitations under the License

use crate::construct_runtime::Pallet;
use proc_macro2::{Span, TokenStream};
use quote::{quote, ToTokens};
use std::str::FromStr;
use syn::{Generics, Ident};

/// Represents the types supported for creating an outer enum.
#[derive(Clone, Copy, PartialEq)]
pub enum OuterEnumType {
	/// Collects the Event enums from all pallets.
	Event,
	/// Collects the Error enums from all pallets.
	Error,
}

impl OuterEnumType {
	/// The name of the structure this enum represents.
	fn struct_name(&self) -> &str {
		match self {
			OuterEnumType::Event => "RuntimeEvent",
			OuterEnumType::Error => "RuntimeError",
		}
	}

	/// The name of the variant (ie `Event` or `Error`).
	fn variant_name(&self) -> &str {
		match self {
			OuterEnumType::Event => "Event",
			OuterEnumType::Error => "Error",
		}
	}
}

impl ToTokens for OuterEnumType {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		match self {
			OuterEnumType::Event => quote!(Event).to_tokens(tokens),
			OuterEnumType::Error => quote!(Error).to_tokens(tokens),
		}
	}
}

/// Create an outer enum that encapsulates all pallets as variants.
///
/// Each variant represents a pallet and contains the corresponding type declared with either:
/// - #[pallet::event] for the [`OuterEnumType::Event`] variant
/// - #[pallet::error] for the [`OuterEnumType::Error`] variant
///
/// The name of the outer enum is prefixed with Runtime, resulting in names like RuntimeEvent
/// or RuntimeError.
///
/// This structure facilitates the decoding process by leveraging the metadata.
///
/// # Example
///
/// The code generate looks like the following for [`OuterEnumType::Event`].
///
/// ```ignore
/// enum RuntimeEvent {
///     #[codec(index = 0)]
///     System(pallet_system::Event),
///
///     #[codec(index = 5)]
///     Balances(pallet_system::Event),
/// }
/// ```
///
/// Notice that the pallet index is preserved using the `#[codec(index = ..)]` attribute.
pub fn expand_outer_enum(
	runtime: &Ident,
	pallet_decls: &[Pallet],
	scrate: &TokenStream,
	enum_ty: OuterEnumType,
) -> syn::Result<TokenStream> {
	// Stores all pallet variants.
	let mut enum_variants = TokenStream::new();
	// Generates the enum conversion between the `Runtime` outer enum and the pallet's enum.
	let mut enum_conversions = TokenStream::new();
	// Specific for events to query via `is_event_part_defined!`.
	let mut query_enum_part_macros = Vec::new();

	let enum_name_str = enum_ty.variant_name();
	let enum_name_ident = Ident::new(enum_ty.struct_name(), Span::call_site());

	for pallet_decl in pallet_decls {
		let Some(pallet_entry) = pallet_decl.find_part(enum_name_str) else { continue };

		let path = &pallet_decl.path;
		let pallet_name = &pallet_decl.name;
		let index = pallet_decl.index;
		let instance = pallet_decl.instance.as_ref();
		let generics = &pallet_entry.generics;

		if instance.is_some() && generics.params.is_empty() {
			let msg = format!(
				"Instantiable pallet with no generic `{}` cannot \
					be constructed: pallet `{}` must have generic `{}`",
				enum_name_str, pallet_name, enum_name_str,
			);
			return Err(syn::Error::new(pallet_name.span(), msg))
		}

		let part_is_generic = !generics.params.is_empty();
		let pallet_enum = match (instance, part_is_generic) {
			(Some(inst), true) => quote!(#path::#enum_ty::<#runtime, #path::#inst>),
			(Some(inst), false) => quote!(#path::#enum_ty::<#path::#inst>),
			(None, true) => quote!(#path::#enum_ty::<#runtime>),
			(None, false) => quote!(#path::#enum_ty),
		};

		enum_variants.extend(expand_enum_variant(
			runtime,
			pallet_decl,
			index,
			instance,
			generics,
			enum_ty,
		));
		enum_conversions.extend(expand_enum_conversion(
			scrate,
			pallet_decl,
			&pallet_enum,
			&enum_name_ident,
		));

		if enum_ty == OuterEnumType::Event {
			query_enum_part_macros.push(quote! {
				#path::__substrate_event_check::is_event_part_defined!(#pallet_name);
			});
		}
	}

	// Derives specific for the event.
	let event_custom_derives =
		if enum_ty == OuterEnumType::Event { quote!(Clone, PartialEq, Eq,) } else { quote!() };

	// Implementation specific for errors.
	let error_custom_impl = generate_error_impl(scrate, enum_ty);

	Ok(quote! {
		#( #query_enum_part_macros )*

		#[derive(
			#event_custom_derives
			#scrate::codec::Encode,
			#scrate::codec::Decode,
			#scrate::scale_info::TypeInfo,
			#scrate::RuntimeDebug,
		)]
		#[allow(non_camel_case_types)]
		pub enum #enum_name_ident {
			#enum_variants
		}

		#enum_conversions

		#error_custom_impl
	})
}

fn expand_enum_variant(
	runtime: &Ident,
	pallet: &Pallet,
	index: u8,
	instance: Option<&Ident>,
	generics: &Generics,
	enum_ty: OuterEnumType,
) -> TokenStream {
	let path = &pallet.path;
	let variant_name = &pallet.name;
	let part_is_generic = !generics.params.is_empty();
	let attr = pallet.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
		let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
			.expect("was successfully parsed before; qed");
		quote! {
			#acc
			#attr
		}
	});

	match instance {
		Some(inst) if part_is_generic => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::#enum_ty<#runtime, #path::#inst>),
		},
		Some(inst) => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::#enum_ty<#path::#inst>),
		},
		None if part_is_generic => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::#enum_ty<#runtime>),
		},
		None => quote! {
			#attr
			#[codec(index = #index)]
			#variant_name(#path::#enum_ty),
		},
	}
}

fn expand_enum_conversion(
	scrate: &TokenStream,
	pallet: &Pallet,
	pallet_enum: &TokenStream,
	enum_name_ident: &Ident,
) -> TokenStream {
	let variant_name = &pallet.name;
	let attr = pallet.cfg_pattern.iter().fold(TokenStream::new(), |acc, pattern| {
		let attr = TokenStream::from_str(&format!("#[cfg({})]", pattern.original()))
			.expect("was successfully parsed before; qed");
		quote! {
			#acc
			#attr
		}
	});

	quote! {
		#attr
		impl From<#pallet_enum> for #enum_name_ident {
			fn from(x: #pallet_enum) -> Self {
				#enum_name_ident
				::#variant_name(x)
			}
		}
		#attr
		impl TryInto<#pallet_enum> for #enum_name_ident {
			type Error = ();

			fn try_into(self) -> #scrate::sp_std::result::Result<#pallet_enum, Self::Error> {
				match self {
					Self::#variant_name(evt) => Ok(evt),
					_ => Err(()),
				}
			}
		}
	}
}

fn generate_error_impl(scrate: &TokenStream, enum_ty: OuterEnumType) -> TokenStream {
	// Implementation is specific to `Error`s.
	if enum_ty == OuterEnumType::Event {
		return quote! {}
	}

	let enum_name_ident = Ident::new(enum_ty.struct_name(), Span::call_site());

	quote! {
		impl #enum_name_ident {
			/// Optionally convert the `DispatchError` into the `RuntimeError`.
			///
			/// Returns `Some` if the error matches the `DispatchError::Module` variant, otherwise `None`.
			pub fn from_dispatch_error(err: #scrate::sp_runtime::DispatchError) -> Option<Self> {
				let #scrate::sp_runtime::DispatchError::Module(module_error) = err else { return None };

				let bytes = #scrate::codec::Encode::encode(&module_error);
				#scrate::codec::Decode::decode(&mut &bytes[..]).ok()
			}
		}
	}
}
