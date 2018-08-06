// Copyright 2018 Parity Technologies (UK) Ltd.
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
use syn::{
	Data, Fields, Index,
	spanned::Spanned,
};

pub fn quote(data: &Data, self_: &TokenStream, dest_: &TokenStream) -> TokenStream {
	let call_site = Span::call_site();
	match *data {
		Data::Struct(ref data) => match data.fields {
			Fields::Named(ref fields) => {
				let recurse = fields.named.iter().map(|f| {
					let name = &f.ident;
					let field = quote_spanned!(call_site => #self_.#name);

					quote_spanned! { f.span() =>
						#dest_.push(&#field);
					}
				});

				quote! {
					#( #recurse )*
				}
			},
			Fields::Unnamed(ref fields) => {
				let recurse = fields.unnamed.iter().enumerate().map(|(i, f)| {
					let index = Index { index: i as u32, span: call_site };
					let field = quote_spanned!(call_site => #self_.#index);
					quote_spanned! { f.span() =>
						#dest_.push(&#field);
					}
				});

				quote! {
					#( #recurse )*
				}
			},
			// Do nothing, we don't encode unit types?
			Fields::Unit => quote! {},
		},
		// TODO [ToDr] Encode enums and unions
		Data::Enum(_) | Data::Union(_) => unimplemented!(),
	}
}


