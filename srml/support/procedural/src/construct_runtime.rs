use proc_macro::TokenStream;
use srml_support_procedural_tools::{ToTokens, Parse, syn_ext as ext};
use syn::{Ident, Token, token};
use quote::quote;
use std::collections::HashMap;


#[derive(Parse, ToTokens, Debug)]
struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_token: Token![where],
	pub where_clauses: ext::Punctuated<WhereLine, Token![,]>
}

#[derive(Parse, ToTokens, Debug)]
struct WhereLine {
	pub name: Ident,
	pub eq_token: Token![=],
	pub module_path: syn::TypePath
}

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	let RuntimeDefinition {
		visibility,
		name,
		where_clauses,
		..
	} = definition;
	let where_type_names = ["Block", "NodeBlock", "UncheckedExtrinsic"]
	let where_data: HashMap<String, syn::TypePath> = where_clauses.inner.iter().map(|where_line| (name.clone(), module_path.clone())).collect();
	quote!(
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct #name;
		impl $crate::sr_primitives::traits::GetNodeBlockType for #name {
			type NodeBlock = $node_block;
		}
		impl $crate::sr_primitives::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = $block;
		}
	)
}
