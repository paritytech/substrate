// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use quote::quote;
use proc_macro2::TokenStream;
use syn::{Data, DeriveInput, parse_quote};

pub fn debug_derive(ast: DeriveInput) -> proc_macro::TokenStream {
	let name_str = ast.ident.to_string();
	let implementation = implementation::derive(&name_str, &ast.data);
	let name = &ast.ident;
	let mut generics = ast.generics.clone();
	let (impl_generics, ty_generics, where_clause) = {
		let wh = generics.make_where_clause();
		for t in ast.generics.type_params() {
			let name = &t.ident;
			wh.predicates.push(parse_quote!{ #name : core::fmt::Debug });
		}
		generics.split_for_impl()
	};
	let gen = quote!{
		impl #impl_generics core::fmt::Debug for #name #ty_generics #where_clause {
			fn fmt(&self, fmt: &mut core::fmt::Formatter) -> core::fmt::Result {
				#implementation
			}
		}
	};

	gen.into()
}

#[cfg(not(feature = "std"))]
mod implementation {
	use super::*;

	/// Derive the inner implementation of `Debug::fmt` function.
	///
	/// Non-std environment. We do nothing to prevent bloating the size of runtime.
	/// Implement `Printable` if you need to print the details.
	pub fn derive(_name_str: &str, _data: &Data) -> TokenStream {
		quote! {
			fmt.write_str("<wasm:stripped>")
		}
	}
}

#[cfg(feature = "std")]
mod implementation {
	use super::*;
	use proc_macro2::Span;
	use syn::{Ident, Index, token::SelfValue};

	/// Derive the inner implementation of `Debug::fmt` function.
	pub fn derive(name_str: &str, data: &Data) -> TokenStream {
		match *data {
			Data::Struct(ref s) => derive_struct(&name_str, &s.fields),
			Data::Union(ref u) => derive_fields(&name_str, Fields::new(u.fields.named.iter(), None)),
			Data::Enum(ref e) => derive_enum(&name_str, &e),
		}
	}

	enum Fields {
		Indexed {
			indices: Vec<Index>,
		},
		Unnamed {
			vars: Vec<Ident>,
		},
		Named {
			names: Vec<Ident>,
			this: Option<SelfValue>,
		},
	}

	impl Fields {
		fn new<'a>(fields: impl Iterator<Item=&'a syn::Field>, this: Option<SelfValue>) -> Self {
			let mut indices = vec![];
			let mut names = vec![];

			for (i, f) in fields.enumerate() {
				if let Some(ident) = f.ident.clone() {
					names.push(ident);
				} else {
					indices.push(Index::from(i));
				}
			}

			if names.is_empty() {
				Self::Indexed {
					indices,
				}
			} else {
				Self::Named {
					names,
					this,
				}
			}
		}
	}

	fn derive_fields<'a>(
		name_str: &str,
		fields: Fields,
	) -> TokenStream {
		match fields {
			Fields::Named { names, this } => {
				let names_str: Vec<_> = names.iter()
					.map(|x| x.to_string())
					.collect();

				let fields = match this {
					None => quote! { #( .field(#names_str, #names) )* },
					Some(this) => quote! { #( .field(#names_str, &#this.#names) )* },
				};

				quote! {
					fmt.debug_struct(#name_str)
						#fields
						.finish()
				}

			},
			Fields::Indexed { indices }  => {
				quote! {
					fmt.debug_tuple(#name_str)
						#( .field(&self.#indices) )*
						.finish()
				}
			},
			Fields::Unnamed { vars }  => {
				quote! {
					fmt.debug_tuple(#name_str)
						#( .field(#vars) )*
						.finish()
				}
			},
		}
	}

	fn derive_enum(
		name: &str,
		e: &syn::DataEnum,
	) -> TokenStream {
		let v = e.variants
			.iter()
			.map(|v| {
				let name = format!("{}::{}", name, v.ident);
				let ident = &v.ident;
				match v.fields {
					syn::Fields::Named(ref f) => {
						let names: Vec<_> = f.named.iter().flat_map(|f| f.ident.clone()).collect();
						let fields_impl = derive_fields(&name, Fields::Named {
							names: names.clone(),
							this: None,
						});
						(ident, (quote!{ { #( ref #names ),* } }, fields_impl))
					},
					syn::Fields::Unnamed(ref f) => {
						let names = f.unnamed.iter()
							.enumerate()
							.map(|(id, _)| Ident::new(&format!("a{}", id), Span::call_site()))
							.collect::<Vec<_>>();
						let fields_impl = derive_fields(&name, Fields::Unnamed { vars: names.clone() });
						(ident, (quote! { ( #( ref #names ),* ) }, fields_impl))
					},
					syn::Fields::Unit => {
						let fields_impl = derive_fields(&name, Fields::Indexed { indices: vec![] });
						(ident, (quote! { }, fields_impl))
					},
				}
			});

		type Vecs<A, B> = (Vec<A>, Vec<B>);
		let (variants, others): Vecs<_, _> = v.unzip();
		let (match_fields, variants_impl): Vecs<_, _> = others.into_iter().unzip();

		quote! {
			match self {
				#( Self::#variants #match_fields => #variants_impl, )*
				_ => Ok(()),
			}
		}
	}

	fn derive_struct(
		name_str: &str,
		fields: &syn::Fields,
	) -> TokenStream {
		match *fields {
			syn::Fields::Named(ref f) => derive_fields(
				name_str,
				Fields::new(f.named.iter(), Some(syn::Token!(self)(Span::call_site()))),
			),
			syn::Fields::Unnamed(ref f) => derive_fields(
				name_str,
				Fields::new(f.unnamed.iter(), None),
			),
			syn::Fields::Unit => derive_fields(
				name_str,
				Fields::Indexed { indices: vec![] },
			),
		}
	}
}
