use proc_macro::TokenStream;
use crate::COUNTER;

pub fn generate_dummy_part_checker(input: TokenStream) -> TokenStream {
	if !input.is_empty() {
		return syn::Error::new(proc_macro2::Span::call_site(), "No arguments expected")
			.to_compile_error().into()
	}

	let count = COUNTER.with(|counter| counter.borrow_mut().inc());

	let genesis_config_macro_ident = syn::Ident::new(
		&format!("__is_genesis_config_defined_{}", count),
		proc_macro2::Span::call_site(),
	);
	let event_macro_ident = syn::Ident::new(
		&format!("__is_event_part_defined_{}", count),
		proc_macro2::Span::call_site(),
	);
	let inherent_macro_ident = syn::Ident::new(
		&format!("__is_inherent_part_defined_{}", count),
		proc_macro2::Span::call_site(),
	);
	let validate_unsigned_macro_ident = syn::Ident::new(
		&format!("__is_validate_unsigned_part_defined_{}", count),
		proc_macro2::Span::call_site(),
	);
	let call_macro_ident = syn::Ident::new(
		&format!("__is_call_part_defined_{}", count),
		proc_macro2::Span::call_site(),
	);

	quote::quote!(
		#[macro_export]
		#[doc(hidden)]
		macro_rules! #genesis_config_macro_ident {
			($pallet_name:ident) => {};
		}
		#[doc(hidden)]
		pub use #genesis_config_macro_ident as __is_genesis_config_defined;

		#[macro_export]
		#[doc(hidden)]
		macro_rules! #event_macro_ident {
			($pallet_name:ident) => {};
		}
		#[doc(hidden)]
		pub use #event_macro_ident as __is_event_part_defined;

		#[macro_export]
		#[doc(hidden)]
		macro_rules! #inherent_macro_ident {
			($pallet_name:ident) => {};
		}
		#[doc(hidden)]
		pub use #inherent_macro_ident as __is_inherent_part_defined;

		#[macro_export]
		#[doc(hidden)]
		macro_rules! #validate_unsigned_macro_ident {
			($pallet_name:ident) => {};
		}
		#[doc(hidden)]
		pub use #validate_unsigned_macro_ident as __is_validate_unsigned_part_defined;

		#[macro_export]
		#[doc(hidden)]
		macro_rules! #call_macro_ident {
			($pallet_name:ident) => {};
		}
		#[doc(hidden)]
		pub use #call_macro_ident as __is_call_part_defined;
	).into()
}
