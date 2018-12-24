use proc_macro2::{Span, TokenStream};
use syn::{
	Data, Field, Fields, Ident, Type,
	Meta, NestedMeta, Lit, Attribute, Variant,
	punctuated::Punctuated,
	spanned::Spanned,
	token::Comma,
};

type FieldsList = Punctuated<Field, Comma>;

fn encode_fields(
	fields: &FieldsList,
) -> TokenStream
{
	let recurse = fields.iter().enumerate().map(|(i, f)| {
		let name = f.ident.as_ref().map(|iden| quote! {
			_substrate_metadata::FieldName::Named(stringify!(#iden).into())
		})
		.unwrap_or(quote! {
			_substrate_metadata::FieldName::Unnamed(#i as u32)
		});
		let ty = &f.ty;
		quote_spanned! { f.span() =>
			_substrate_metadata::FieldMetadata {
				name: #name,
				ty: <#ty>::type_metadata()
			}
		}
	});

	quote! {
		_substrate_metadata::TypeMetadata::Struct(vec![#( #recurse, )*])
	}
}

pub fn quote(data: &Data, type_name: &Ident) -> TokenStream {
	let call_site = Span::call_site();
	let res = match *data {
		Data::Struct(ref data) => {
			match data.fields {
				Fields::Named(ref fields) => encode_fields(
					&fields.named,
				),
				Fields::Unnamed(ref fields) => encode_fields(
					&fields.unnamed,
				),
				Fields::Unit => quote_spanned! { call_site =>
					_substrate_metadata::TypeMetadata::Struct(vec![])
				},
			}
		},
		Data::Enum(ref data) => {
			let recurse = data.variants.iter().enumerate().map(|(i, f)| {
				let name = &f.ident;
				let index = index(f, i);
				match f.fields {
					Fields::Named(ref fields) => {
						let field_name = |ty: &Type| {
							quote_spanned!(call_site => #ty)
						};
						let fields = fields.named
							.iter()
							.map(|f| {
								let ty = field_name(&f.ty);
								let name = &f.ident;
								quote_spanned! { f.span() =>
									_substrate_metadata::FieldMetadata {
										name: _substrate_metadata::FieldName::Named(stringify!(#name).into()),
										ty: <#ty>::type_metadata()
									}
								}
							});

						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: vec![#( #fields, )*]
							}
						}
					},
					Fields::Unnamed(ref fields) => {
						let field_name = |ty: &Type| {
							quote_spanned!(call_site => #ty)
						};
						let fields = fields.unnamed
							.iter()
							.enumerate()
							.map(|(i, f)| {
								let ty = field_name(&f.ty);
								quote! {
									_substrate_metadata::FieldMetadata {
										name: _substrate_metadata::FieldName::Unnamed(#i as u32),
										ty: <#ty>::type_metadata()
									}
								}
							});

						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: vec![#( #fields, )*]
							}
						}
					},
					Fields::Unit => {
						quote_spanned! { f.span() =>
							_substrate_metadata::EnumVariantMetadata {
								name: stringify!(#name).into(),
								index: #index as u32,
								fields: Vec::new()
							}
						}
					},
				}
			});

			quote! {
				_substrate_metadata::TypeMetadata::Enum(vec![#( #recurse, )*])
			}
		},
		Data::Union(_) => panic!("Union types are not supported."),
	};
	quote! {
		_substrate_metadata::Metadata {
			name: stringify!(#type_name).into(),
			kind: #res
		}
	}
}

fn find_meta_item<'a, F, R, I>(itr: I, pred: F) -> Option<R> where
	F: FnMut(&NestedMeta) -> Option<R> + Clone,
	I: Iterator<Item=&'a Attribute>
{
	itr.filter_map(|attr| {
		let pair = attr.path.segments.first()?;
		let seg = pair.value();
		if seg.ident == "codec" {
			let meta = attr.interpret_meta();
			if let Some(Meta::List(ref meta_list)) = meta {
				return meta_list.nested.iter().filter_map(pred.clone()).next();
			}
		}

		None
	}).next()
}

fn index(v: &Variant, i: usize) -> TokenStream {
	// look for an index in attributes
	let index = find_meta_item(v.attrs.iter(), |meta| {
		if let NestedMeta::Meta(Meta::NameValue(ref nv)) = meta {
			if nv.ident == "index" {
				if let Lit::Str(ref s) = nv.lit {
					let byte: u8 = s.value().parse().expect("Numeric index expected.");
					return Some(byte)
				}
			}
		}

		None
	});

	// then fallback to discriminant or just index
	index.map(|i| quote! { #i })
		.unwrap_or_else(|| v.discriminant
			.as_ref()
			.map(|&(_, ref expr)| quote! { #expr })
			.unwrap_or_else(|| quote! { #i })
		)
}
