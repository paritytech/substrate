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
pub struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_section: WhereSection,
	pub modules: ext::Braces<ext::Punctuated<DeclModulesLine, Token![,]>>,
}

#[derive(Parse, ToTokens, Debug)]
pub struct WhereSection {
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
pub struct DeclModulesLine {
	pub name: Ident,
	pub name_colon: Token![:],
	pub module: Ident,
	pub module_instance: ext::Opt<ModuleInstance>,
	pub module_details: ext::Opt<ModuleDetails>,
}

#[derive(Parse, ToTokens, Debug)]
pub struct ModuleInstance {
	pub colons: Token![::],
	pub lt: Token![<],
	pub name: Ident,
	pub gt: Token![>],
}

#[derive(Parse, ToTokens, Debug)]
pub struct ModuleDetails {
	pub colons: Token![::],
	pub entries: ext::Braces<ext::Punctuated<ModuleEntryWrapper, Token![,]>>,
}

#[derive(ToTokens, Debug)]
pub struct ModuleEntryWrapper {
	pub inner: ModuleEntry,
}

impl Parse for ModuleEntryWrapper {
	fn parse(input: ParseStream) -> Result<Self> {
		ModuleEntry::parse(input)
			.map(|inner| ModuleEntryWrapper { inner })
			.map_err(|_| input.error("Expected `default` or module export name (e.g. Call, Event, etc.)"))
	}
}

#[derive(Parse, ToTokens, Debug)]
pub enum ModuleEntry {
	Default(Token![default]),
	Part(ModulePart),
}

#[derive(Parse, ToTokens, Debug)]
pub struct ModulePart {
	pub name: Ident,
	// This deviates from macro $( <$modules_generic:ident> )*
	pub generics: ext::Opt<syn::Generics>,
	pub args: ext::Opt<ext::Parens<ext::Punctuated<Ident, Token![,]>>>,
}
