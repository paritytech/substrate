use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{Error, Expr, ItemFn};

#[proc_macro_attribute]
pub fn substrate_cli_node_name(arg: TokenStream, item: TokenStream) -> TokenStream {
	let item_fn = syn::parse_macro_input!(item as ItemFn);

	if arg.is_empty() {
		return Error::new(Span::call_site(), "missing expression (name of the node)")
			.to_compile_error()
			.into();
	}

	let name = syn::parse_macro_input!(arg as Expr);

	let ItemFn {
		attrs,
		vis,
		sig,
		block,
	} = item_fn;

	(quote! {
		#(#attrs)*
		#vis #sig {
			// TODO: use whatever imported name for the crate
			let span = ::sc_cli::tracing::info_span!("substrate-node", name = #name);
			let _enter = span.enter();

			#block
		}
	})
	.into()
}
