extern crate proc_macro;
extern crate proc_macro2;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{DeriveInput, Generics, GenericParam, Ident};

mod encode;

const ENCODE_ERR: &str = "derive(EncodeMetadata) failed";

#[proc_macro_derive(EncodeMetadata)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
	let input: DeriveInput = syn::parse(input).expect(ENCODE_ERR);
	let name = &input.ident;

	let generics = add_trait_bounds(input.generics, parse_quote!(_substrate_metadata::EncodeMetadata));
	let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

	let metadata = encode::quote(&input.data, name);

	let impl_block = quote! {
		impl #impl_generics _substrate_metadata::EncodeMetadata for #name #ty_generics #where_clause {
			fn type_metadata() -> _substrate_metadata::Metadata {
				#metadata
			}
		}
	};

	let mut new_name = "_IMPL_ENCODEMETADATA_FOR_".to_string();
	new_name.push_str(name.to_string().trim_left_matches("r#"));
	let dummy_const = Ident::new(&new_name, Span::call_site());

	let generated = quote! {
		#[allow(non_upper_case_globals, unused_attributes, unused_qualifications)]
		const #dummy_const: () = {
			#[allow(unknown_lints)]
			#[cfg_attr(feature = "cargo-clippy", allow(useless_attribute))]
			#[allow(rust_2018_idioms)]
			extern crate substrate_metadata as _substrate_metadata;
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
