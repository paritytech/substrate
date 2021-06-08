use proc_macro::TokenStream;

pub fn generate_dummy_part_checker(input: TokenStream) -> TokenStream {
	if !input.is_empty() {
		return syn::Error::new(proc_macro2::Span::call_site(), "No arguments expected")
			.to_compile_error().into()
	}

	thread_local! {
		static COUNTER: std::cell::RefCell<u64> = std::cell::RefCell::new(0u64);
	}

	let count = COUNTER.with(|counter| {
		*counter.borrow_mut() += 1;
		*counter.borrow()
	});
	let genesis_config_macro_ident = syn::Ident::new(&format!("__is_genesis_config_defined_{}", count), proc_macro2::Span::call_site());
	let event_macro_ident = syn::Ident::new(&format!("__is_event_part_defined_{}", count), proc_macro2::Span::call_site());
	let inherent_macro_ident = syn::Ident::new(&format!("__is_inherent_part_defined_{}", count), proc_macro2::Span::call_site());
	let validate_unsigned_macro_ident = syn::Ident::new(&format!("__is_validate_unsigned_part_defined_{}", count), proc_macro2::Span::call_site());
	let call_macro_ident = syn::Ident::new(&format!("__is_call_part_defined_{}", count), proc_macro2::Span::call_site());

	quote::quote!(
		#[macro_export]
		macro_rules! #genesis_config_macro_ident {
			($pallet_name:ident) => {};
		}
		pub use #genesis_config_macro_ident as __is_genesis_config_defined;

		#[macro_export]
		macro_rules! #event_macro_ident {
			($pallet_name:ident) => {};
		}
		pub use #event_macro_ident as __is_event_part_defined;

		#[macro_export]
		macro_rules! #inherent_macro_ident {
			($pallet_name:ident) => {};
		}
		pub use #inherent_macro_ident as __is_inherent_part_defined;

		#[macro_export]
		macro_rules! #validate_unsigned_macro_ident {
			($pallet_name:ident) => {};
		}
		pub use #validate_unsigned_macro_ident as __is_validate_unsigned_part_defined;

		#[macro_export]
		macro_rules! #call_macro_ident {
			($pallet_name:ident) => {};
		}
		pub use #call_macro_ident as __is_call_part_defined;
	).into()
}
