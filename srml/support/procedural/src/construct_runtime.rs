use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use srml_support_procedural_tools::{syn_ext as ext, Parse, ToTokens};
use std::collections::{HashMap, HashSet};
use syn::{token, Ident, Token, spanned::Spanned, parse::{Parse, ParseStream}, Result};

mod keyword {
	syn::custom_keyword!(Block);
	syn::custom_keyword!(NodeBlock);
	syn::custom_keyword!(UncheckedExtrinsic);
}

#[derive(Parse, ToTokens, Debug)]
struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_section: WhereSection,
	pub modules: ext::Braces<ext::Punctuated<DeclModulesLine, Token![;]>>
}

#[derive(Parse, ToTokens, Debug)]
struct WhereSection {
	pub token: Token![where],
	pub block_token: keyword::Block,
	pub block_eq: Token![=],
	pub block: syn::TypePath,
	pub block_sep: Token![,],
	pub node_block_token: keyword::NodeBlock,
	pub node_block_eq: Token![=],
	pub node_block: syn::TypePath,
	pub node_block_sep: Token![,],
	pub unchecked_extrinsic_token: keyword::UncheckedExtrinsic,
	pub unchecked_extrinsic_eq: Token![=],
	pub unchecked_extrinsic: syn::TypePath,
}

#[derive(Parse, ToTokens, Debug)]
struct DeclModulesLine {
	pub name: Ident,
}

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	let RuntimeDefinition {
		name, where_section: WhereSection { block, node_block, unchecked_extrinsic, .. }, ..
	} = definition;
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
