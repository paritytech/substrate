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

//! Derives type metadata information to enable self-descriptive codec

extern crate proc_macro;

use syn::parse_quote;
use quote::{quote};

use proc_macro::TokenStream;
use proc_macro2::{Span};
use syn::{DeriveInput, Generics, Ident, GenericParam};

mod encode;

#[proc_macro_derive(EncodeMetadata)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	let generics = add_trait_bounds(input.generics, parse_quote!(_substrate_metadata::EncodeMetadata));

	let generic_types = generics.params.iter().map(|param| {
		if let GenericParam::Type(ref type_param) = *param {
			Some(type_param.ident.clone())
		} else {
			None
		}
	})
	.filter(Option::is_some)
	.collect::<Vec<_>>();

	let name = &input.ident;
	let impl_type_name = if generic_types.is_empty() {
		quote! {
			fn type_name() -> _substrate_metadata::MetadataName {
				_substrate_metadata::MetadataName::Custom(module_path!().into(), stringify!(#name).into())
			}
		}
	} else {
		let generic_type_names = generic_types.into_iter().map(|t| {
			quote! {
				<#t as _substrate_metadata::EncodeMetadata>::type_name()
			}
		});
		quote! {
			fn type_name() -> _substrate_metadata::MetadataName {
				_substrate_metadata::MetadataName::CustomWithGenerics(module_path!().into(), stringify!(#name).into(), vec![
					#( #generic_type_names ),*
				])
			}
		}
	};

	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let registry = quote!(registry);

	let metadata_kind = encode::quote(&input.data, &registry);

	let impl_block = quote! {
		impl #impl_generics _substrate_metadata::EncodeMetadata for #name #ty_generics #where_clause {
			#impl_type_name

			fn type_metadata_kind(registry: &mut _substrate_metadata::MetadataRegistry) -> _substrate_metadata::TypeMetadataKind {
				#metadata_kind
			}
		}
	};

	let mut new_name = "_IMPL_ENCODEMETADATA_FOR_".to_string();
	new_name.push_str(name.to_string().trim_start_matches("r#"));
	let dummy_const = Ident::new(&new_name, Span::call_site());

	let generated = quote! {
		#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
		const #dummy_const: () = {
			#[allow(unknown_lints)]
			#[cfg_attr(feature = "cargo-clippy", allow(useless_attribute))]
			#[allow(rust_2018_idioms)]
			extern crate substrate_metadata as _substrate_metadata;
			use _substrate_metadata::rstd::prelude::*;
			#impl_block
		};
	};

	generated.into()
}

fn add_trait_bounds(mut generics: Generics, bounds: syn::TypeParamBound) -> Generics {
	for param in &mut generics.params {
		if let GenericParam::Type(ref mut type_param) = *param {
			type_param.bounds.push(bounds.clone());
		}
	}
	generics
}
