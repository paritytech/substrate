use proc_macro::TokenStream;
use quote::quote;
use syn::{parse_macro_input, ItemFn};

pub fn benchmark(_attrs: TokenStream, tokens: TokenStream) -> TokenStream {
	let _item_fn = parse_macro_input!(tokens as ItemFn);
	quote!("").into()
}
