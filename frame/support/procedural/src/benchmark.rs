use proc_macro::TokenStream;
use quote::quote;

pub fn benchmark(_tokens: TokenStream) -> TokenStream {
	quote!("").into()
}
