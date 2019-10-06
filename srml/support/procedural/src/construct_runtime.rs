use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use srml_support_procedural_tools::{syn_ext as ext, Parse, ToTokens};
use std::collections::{HashMap, HashSet};
use syn::{token, Ident, Token, spanned::Spanned};

#[derive(Parse, ToTokens, Debug)]
struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_token: Token![where],
	pub where_clauses: ext::Punctuated<WhereLine, Token![,]>,
}

#[derive(Parse, ToTokens, Debug)]
struct WhereLine {
	pub name: Ident,
	pub eq_token: Token![=],
	pub module_path: syn::TypePath,
}

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	let RuntimeDefinition {
		name, where_clauses, where_token, ..
	} = definition;
	let (block, node_block, unchecked_extrinsic) = match extract_where_types(where_clauses, where_token.span()) {
		Ok(x) => x,
		Err(e) => return e.to_compile_error().into()
	};
	quote!(
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct #name;
		impl $crate::sr_primitives::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl $crate::sr_primitives::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}
	)
	.into()
}

fn extract_where_types(
	where_clauses: ext::Punctuated<WhereLine, Token![,]>,
	span: Span,
) -> syn::Result<(syn::TypePath, syn::TypePath, syn::TypePath)> {
	let where_data: HashMap<String, syn::TypePath> = where_clauses
		.inner
		.iter()
		.map(|WhereLine { name, module_path, .. }| (format!("{}", name), module_path.clone()))
		.collect();
	let where_names: HashSet<String> = where_data.keys().cloned().collect();
	let required_where_names: HashSet<String> = ["Block", "NodeBlock", "UncheckedExtrinsic"]
		.into_iter()
		.map(ToString::to_string)
		.collect();

	let missing_names: Vec<&str> = required_where_names
		.difference(&where_names)
		.map(String::as_str)
		.collect();
	if missing_names.len() > 0 {
		let message = format!(
			"The following params are missing in where clause: {}",
			missing_names.as_slice().join(", ")
		);
		return Err(syn::Error::new(span, message));
	}

	let redundant_names: Vec<&str> = where_names
		.difference(&required_where_names)
		.map(String::as_str)
		.collect();
	if missing_names.len() > 0 {
		let message = format!(
			"The following params should not be in where clause: {}",
			redundant_names.as_slice().join(", ")
		);
		return Err(syn::Error::new(span, message));
	}

	Ok((
		where_data.get("Block").cloned().unwrap(),
		where_data.get("NodeBlock").cloned().unwrap(),
		where_data.get("UncheckedExtrinsic").cloned().unwrap(),
	))
}
