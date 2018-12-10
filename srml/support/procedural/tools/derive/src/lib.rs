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

// tag::description[]
//! Use to derive parsing for parsing struct.
// end::description[]


#![recursion_limit = "128"]

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

extern crate proc_macro;
extern crate proc_macro2;

use proc_macro::TokenStream;
use proc_macro2::Span;


pub(crate) fn fields_idents(
	fields: impl Iterator<Item = syn::Field>,
) -> impl Iterator<Item = proc_macro2::TokenStream> {
	fields.enumerate().map(|(ix, field)| {
		field.ident.clone().map(|i| quote!{#i}).unwrap_or_else(|| {
			let f_ix: syn::Ident = syn::Ident::new(&format!("f_{}", ix), Span::call_site());
			quote!( #f_ix )
		})
	})
}

pub(crate) fn fields_access(
	fields: impl Iterator<Item = syn::Field>,
) -> impl Iterator<Item = proc_macro2::TokenStream> {
	fields.enumerate().map(|(ix, field)| {
		field.ident.clone().map(|i| quote!( #i )).unwrap_or_else(|| {
			let f_ix: syn::Index = syn::Index {
				index: ix as u32,
				span: Span::call_site(),
			};
			quote!( #f_ix )
		})
	})
}

/// self defined parsing struct (use where clause on struct for it: not meant for good struct
/// design but fast parse impl).
#[proc_macro_derive(ParseStruct)]
pub fn derive_parse_struct(input: TokenStream) -> TokenStream {
	let syn::ItemStruct {
		ident,
		generics,
		fields,
		..
	} = parse_macro_input!(input as syn::ItemStruct);
	let field_names = {
		let name = fields_idents(fields.iter().map(Clone::clone));
		quote!{
			#(
				#name,
			)*
		}
	};
	let field = fields_idents(fields.iter().map(Clone::clone));
	let tokens = quote! {
		impl #generics syn::parse::Parse for #ident #generics {
			fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<Self> {
				#(
					let #field = input.parse()?;
				)*
				Ok(Self {
					#field_names
				})
			}
		}
	};
	tokens.into()
}

#[proc_macro_derive(ToTokensStruct)]
pub fn derive_totokens_struct(input: TokenStream) -> TokenStream {
	let syn::ItemStruct {
		ident,
		generics,
		fields,
		..
	} = parse_macro_input!(input as syn::ItemStruct);
	let fields = fields_access(fields.iter().map(Clone::clone));
	let tokens = quote! {

		impl #generics quote::ToTokens for #ident #generics {
			fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
				#(
					self.#fields.to_tokens(tokens);
				)*
			}
		}

	};
	tokens.into()
}


/// self defined parsing enum, variant are tested in order of definition.
/// Empty variant allways true.
/// Please use carefully, this will fully parse successfull variant twice.
#[proc_macro_derive(ParseEnum)]
pub fn derive_parse_enum(input: TokenStream) -> TokenStream {

	let syn::ItemEnum {
		ident,
		generics,
		variants,
		..
	} = parse_macro_input!(input as syn::ItemEnum);
	let variants = variants.iter().map(|v| {
		let variant_ident = v.ident.clone();
		let fields_build = if v.fields.iter().count() > 0 {
			let fields_id = fields_idents(v.fields.iter().map(Clone::clone));
			quote!( (#(#fields_id), *) )
		} else {
			quote!()
		};

		let fields_procs = fields_idents(v.fields.iter().map(Clone::clone))
			.map(|fident| {
				quote!{
					let mut #fident = match fork.parse() {
						Ok(r) => r,
						Err(_e) => break,
					};
				}
			});
		let fields_procs_again = fields_idents(v.fields.iter().map(Clone::clone))
			.map(|fident| {
				quote!{
					#fident = input.parse().expect("was parsed just before");
				}
			});

		// double parse to update input cursor position
		// next syn crate version should be checked for a way
		// to copy position/state from a fork
		quote!{
			let mut fork = input.fork();
			loop {
				#(#fields_procs)*
				#(#fields_procs_again)*
				return Ok(#ident::#variant_ident#fields_build);
			}
		}
	});

	let tokens = quote! {
		impl #generics syn::parse::Parse for #ident #generics {
			fn parse(input: syn::parse::ParseStream) -> syn::parse::Result<Self> {
				#(
					#variants
				)*
				// no early return from any variants
				Err(
					syn::parse::Error::new(
						proc_macro2::Span::call_site(),
						"derived enum no matching variants"
					)
				)
			}
		}

	};
	tokens.into()
}

/// only output field (empty field act as a None)
#[proc_macro_derive(ToTokensEnum)]
pub fn derive_totokens_enum(input: TokenStream) -> TokenStream {
	let syn::ItemEnum {
		ident,
		generics,
		variants,
		..
	} = parse_macro_input!(input as syn::ItemEnum);
	let variants = variants.iter().map(|v| {
		let v_ident = v.ident.clone();
		let fields_build = if v.fields.iter().count() > 0 {
			let fields_id = fields_idents(v.fields.iter().map(Clone::clone));
			quote!( (#(#fields_id), *) )
		} else {
			quote!()
		};
		let field = fields_idents(v.fields.iter().map(Clone::clone));
		quote! {
			#ident::#v_ident#fields_build => {
				#(
					#field.to_tokens(tokens);
				)*
			},
		}
	});
	let tokens = quote! {
		impl #generics quote::ToTokens for #ident #generics {
			fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
				match self {
					#(
						#variants
					)*
				}
			}
		}
	};

	tokens.into()
}
