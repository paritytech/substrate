use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use srml_support_procedural_tools::{syn_ext as ext, Parse, ToTokens};
use std::collections::{HashMap, HashSet};
use syn::{
	parse::{Parse, ParseStream},
	spanned::Spanned,
	token, Ident, Result, Token,
};

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
	pub modules: ext::Braces<ext::Punctuated<DeclModulesLine, Token![,]>>,
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
	pub name_colon: Token![:],
	pub module: Ident,
	pub module_instance: ext::Opt<ModuleInstance>,
	pub module_details: ext::Opt<ModuleDetails>,
}

#[derive(Parse, ToTokens, Debug)]
struct ModuleInstance {
	pub colons: Token![::],
	pub lt: Token![<],
	pub name: Ident,
	pub gt: Token![>],
}

#[derive(Parse, ToTokens, Debug)]
struct ModuleDetails {
	pub colons: Token![::],
	pub entries: ext::Braces<ext::Punctuated<ModuleEntryWrapper, Token![,]>>
}

#[derive(ToTokens, Debug)]
struct ModuleEntryWrapper {
	pub inner: ModuleEntry,
}

impl Parse for ModuleEntryWrapper {
	fn parse(input: ParseStream) -> Result<Self> {
		ModuleEntry::parse(input).map(|inner| ModuleEntryWrapper { inner } ).map_err(|_| input.error("Expected `default` or module export name (e.g. Call, Event, etc.)"))
	}
}

#[derive(Parse, ToTokens, Debug)]
enum ModuleEntry {
	Default(Token![default]),
	Part(ModulePart),
}

#[derive(Parse, ToTokens, Debug)]
struct ModulePart {
	pub name: Ident,
	// This deviates from macro $( <$modules_generic:ident> )*
	pub generics: ext::Opt<syn::Generics>,
	pub args: ext::Opt<ext::Parens<ext::Punctuated<Ident, Token![,]>>>,
}

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	let RuntimeDefinition {
		name,
		where_section: WhereSection {
			block,
			node_block,
			unchecked_extrinsic,
			..
		},
		..
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
