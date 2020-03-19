extern crate proc_macro;

mod spec_factory;
mod substrate_cli_params;

use proc_macro_error::{proc_macro_error};

#[proc_macro_attribute]
#[proc_macro_error]
pub fn spec_factory(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	spec_factory::spec_factory(a, i).into()
}

#[proc_macro_attribute]
#[proc_macro_error]
pub fn substrate_cli_params(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro::TokenStream {
	substrate_cli_params::substrate_cli_params(a, i).into()
}
