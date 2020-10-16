use proc_macro::TokenStream;
use proc_macro2::Span;
use proc_macro_crate::crate_name;
use quote::quote;
use syn::{Error, Expr, Ident, ItemFn};

#[proc_macro_attribute]
pub fn substrate_cli_node_name(arg: TokenStream, item: TokenStream) -> TokenStream {
	let item_fn = syn::parse_macro_input!(item as ItemFn);

	if arg.is_empty() {
		return Error::new(Span::call_site(), "missing expression (name of the node)")
			.to_compile_error()
			.into();
	}

	let name = syn::parse_macro_input!(arg as Expr);

	let crate_name = if std::env::var("CARGO_PKG_NAME").unwrap() == "sc-cli" {
		Ident::new("sc_cli", Span::call_site().into())
	} else {
		let crate_name = match crate_name("sc-cli") {
			Ok(x) => x,
			Err(err) => return Error::new(Span::call_site(), err).to_compile_error().into(),
		};

		Ident::new(&crate_name, Span::call_site().into())
	};

	let ItemFn {
		attrs,
		vis,
		sig,
		block,
	} = item_fn;

	(quote! {
		#(#attrs)*
		#vis #sig {
			let span = #crate_name::tracing::info_span!("substrate-node", name = #name);
			let _enter = span.enter();

			#block
		}
	})
	.into()
}
