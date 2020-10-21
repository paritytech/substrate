use proc_macro2::TokenStream;
use proc_macro_error::{proc_macro_error, abort};
use quote::{quote, quote_spanned};
use syn::spanned::Spanned;
use syn::{parse_macro_input, Data, DataStruct, DeriveInput, Fields, Ident};

/// This derives `Debug` for a struct where each field must be of some numeric type.
/// It interprets each field as its represents some weight and formats it as times so that
/// it is readable by humans.
#[proc_macro_derive(WeightDebug)]
#[proc_macro_error]
pub fn derive_weight_debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	derive_debug(input, format_weight)
}

/// This is basically identical to the std libs Debug derive but without adding any
/// bounds to existing generics.
#[proc_macro_derive(ScheduleDebug)]
#[proc_macro_error]
pub fn derive_schedule_debug(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	derive_debug(input, format_default)
}

fn derive_debug(
	input: proc_macro::TokenStream,
	fmt: impl Fn(&Ident) -> TokenStream
) -> proc_macro::TokenStream
{
	let input = parse_macro_input!(input as DeriveInput);
	let name = &input.ident;
	let (impl_generics, ty_generics, where_clause) = input.generics.split_for_impl();
	let data = if let Data::Struct(data) = &input.data {
		data
	} else {
		abort!(name, "WeightDebug is only supported for structs.");
	};
	let fields = iterate_fields(data, fmt);

	let tokens = quote! {
		impl #impl_generics std::fmt::Debug for #name #ty_generics #where_clause {
			fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
				use ::sp_runtime::{FixedPointNumber, FixedU128 as Fixed};
				let mut formatter = formatter.debug_struct(stringify!(#name));
				#fields
				formatter.finish()
			}
		}
	};

	tokens.into()
}

fn iterate_fields(data: &DataStruct, fmt: impl Fn(&Ident) -> TokenStream) -> TokenStream {
	match &data.fields {
		Fields::Named(fields) => {
			let recurse = fields.named
			.iter()
			.filter_map(|f| {
				let name = f.ident.as_ref()?;
				if name.to_string().starts_with('_') {
					return None;
				}
				let value = fmt(name);
				let ret = quote_spanned!{ f.span() =>
					formatter.field(stringify!(#name), #value);
				};
				Some(ret)
			});
			quote!{
				#( #recurse )*
			}
		}
		Fields::Unnamed(fields) => abort!(fields, "Unnamed fields are not supported"),
		Fields::Unit => quote!(),
	}
}

fn format_weight(field: &Ident) -> TokenStream {
	quote_spanned! { field.span() =>
		&if self.#field > 1_000_000_000 {
			format!(
				"{:.1?} ms",
				Fixed::saturating_from_rational(self.#field, 1_000_000_000).to_fraction()
			)
		} else if self.#field > 1_000_000 {
			format!(
				"{:.1?} µs",
				Fixed::saturating_from_rational(self.#field, 1_000_000).to_fraction()
			)
		} else if self.#field > 1_000 {
			format!(
				"{:.1?} ns",
				Fixed::saturating_from_rational(self.#field, 1_000).to_fraction()
			)
		} else {
			format!("{} ps", self.#field)
		}
	}
}

fn format_default(field: &Ident) -> TokenStream {
	quote_spanned! { field.span() =>
		&self.#field
	}
}
