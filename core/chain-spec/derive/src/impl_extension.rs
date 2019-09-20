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

use proc_macro2::{Span, TokenStream};
use quote::quote;
use syn::{DeriveInput, Ident, Error};
use proc_macro_crate::crate_name;

const CRATE_NAME: &str = "substrate-chain-spec";

pub fn impl_extension_derive(ast: &DeriveInput) -> proc_macro::TokenStream {
	let err = || {
		let err = Error::new(
			Span::call_site(),
			"ChainSpecExtension is only avaible for structs with named fields."
		).to_compile_error();
		quote!( #err ).into()
	};

	let data = match &ast.data {
		syn::Data::Struct(ref data) => data,
		_ => return err(),
	};

	let fields = match &data.fields {
		syn::Fields::Named(ref named) => named,
		_ => return err(),
	};

	let name = &ast.ident;
	let crate_name = match crate_name(CRATE_NAME) {
		Ok(chain_spec_name) => chain_spec_name,
		Err(e) => if std::env::var("CARGO_PKG_NAME").unwrap() == CRATE_NAME {
			"crate".to_string()
		} else {
			let err = Error::new(Span::call_site(), &e).to_compile_error();
			return quote!( #err ).into()
		},
	};
	let crate_name = Ident::new(&crate_name, Span::call_site());

	let (impl_generics, ty_generics, where_clause) = ast.generics.split_for_impl();
	let fork_name = Ident::new(&format!("{}Fork", name), Span::call_site());
	let field_names = fields.named.iter().flat_map(|x| x.ident.as_ref()).collect::<Vec<_>>();
	let field_types = fields.named.iter().map(|x| &x.ty).collect::<Vec<_>>();

	let fork_fields = generate_fork_fields(&crate_name, &field_names, &field_types);
	let to_fork = generate_base_to_fork(&fork_name, &field_names);
	let combine_with = generate_combine_with(&field_names);
	let to_base = generate_fork_to_base(name, &field_names);

	let gen = quote! {
		#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
		pub struct #fork_name #ty_generics #where_clause {
			#fork_fields
		}

		impl #impl_generics #crate_name::Extension for #name #ty_generics #where_clause {
			type Fork = #fork_name #ty_generics;

			fn to_fork(self) -> Self::Fork {
				use #crate_name::Extension;
				#to_fork
			}
		}

		impl #impl_generics #crate_name::Fork for #fork_name #ty_generics #where_clause {
			type Base = #name #ty_generics;

			fn combine_with(&mut self, other: Self) {
				use #crate_name::Fork;
				#combine_with
			}

			fn to_base(self) -> Option<Self::Base> {
				use #crate_name::Fork;
				#to_base
			}
		}
	};

	gen.into()
}

fn generate_fork_fields(
	crate_name: &Ident,
	names: &[&Ident],
	types: &[&syn::Type],
) -> TokenStream {
	let crate_name = std::iter::repeat(crate_name);
	quote! {
		#( pub #names: Option<<#types as #crate_name::Extension>::Fork>, )*
	}
}

fn generate_base_to_fork(
	fork_name: &Ident,
	names: &[&Ident],
) -> TokenStream {
	let names2 = names.to_vec();

	quote!{
		#fork_name {
			#( #names: Some(self.#names2.to_fork()), )*
		}
	}
}

fn generate_combine_with(
	names: &[&Ident],
) -> TokenStream {
	let names2 = names.to_vec();

	quote!{
		#( self.#names.combine_with(other.#names2); )*
	}
}

fn generate_fork_to_base(
	fork: &Ident,
	names: &[&Ident],
) -> TokenStream {
	let names2 = names.to_vec();

	quote!{
		Some(#fork {
			#( #names: self.#names2?.to_base()?, )*
		})
	}
}

