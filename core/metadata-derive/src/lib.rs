extern crate proc_macro;
extern crate proc_macro2;

#[macro_use]
extern crate syn;

#[macro_use]
extern crate quote;

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{DeriveInput, Generics, Ident};

mod encode;


#[proc_macro_derive(EncodeMetadata)]
pub fn encode_derive(input: TokenStream) -> TokenStream {
	let mut input: DeriveInput = match syn::parse(input) {
		Ok(input) => input,
		Err(e) => return e.to_compile_error().into(),
	};

	if let Err(e) = add_trait_bounds(&mut input.generics, &input.data, parse_quote!(_substrate_metadata::EncodeMetadata)) {
		return e.to_compile_error().into();
	}

	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();

	let registry = quote!(registry);

	let metadata_kind = encode::quote(&input.data, &registry);

	let impl_block = quote! {
		impl #impl_generics _substrate_metadata::EncodeMetadata for #name #ty_generics #where_clause {
			fn type_name() -> _substrate_metadata::MetadataName {
				_substrate_metadata::MetadataName::Custom(module_path!().into(), stringify!(#name).into())
			}

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
			#impl_block
		};
	};

	generated.into()
}

fn add_trait_bounds(generics: &mut Generics, data: &syn::Data, bound: syn::Path) -> Result<(), syn::Error> {
	if generics.params.is_empty() {
		return Ok(());
	}

	let types = collect_types(&data)?;
	if !types.is_empty() {
		let where_clause = generics.make_where_clause();

		types.into_iter().for_each(|ty| where_clause.predicates.push(parse_quote!(#ty : #bound)));
	}

	Ok(())
}

fn collect_types(data: &syn::Data) -> Result<Vec<syn::Type>, syn::Error> {
	use syn::*;

	let types = match *data {
		Data::Struct(ref data) => match &data.fields {
			| Fields::Named(FieldsNamed { named: fields , .. })
			| Fields::Unnamed(FieldsUnnamed { unnamed: fields, .. }) => {
				fields.iter().map(|f| f.ty.clone()).collect()
			},

			Fields::Unit => { Vec::new() },
		},

		Data::Enum(ref data) => data.variants.iter().flat_map(|variant| {
			match &variant.fields {
				| Fields::Named(FieldsNamed { named: fields , .. })
				| Fields::Unnamed(FieldsUnnamed { unnamed: fields, .. }) => {
					fields.iter().map(|f| f.ty.clone()).collect()
				},

				Fields::Unit => { Vec::new() },
			}
		}).collect(),

		Data::Union(_) => return Err(Error::new(Span::call_site(), "Union types are not supported.")),
	};

	Ok(types)
}

