use self::keywords::message;

use super::helper;
use frame_support_procedural_tools::get_doc_literals;

use derive_syn_parse::Parse;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
	parenthesized,
	parse::{Nothing, ParseStream},
	parse_quote,
	punctuated::Punctuated,
	spanned::Spanned,
	token::{Colon2, Comma, Gt, Lt, Paren},
	Attribute, Error, Expr, ExprBlock, ExprCall, ExprPath, FnArg, Item, ItemFn, ItemMod, LitInt,
	Pat, Path, PathArguments, PathSegment, Result, ReturnType, Signature, Stmt, Token, Type,
	TypePath, Visibility, WhereClause,
};

mod keywords {
	use syn::custom_keyword;

	custom_keyword!(storage);
	custom_keyword!(message);
}

#[derive(Clone, Debug)]
struct InkAttrs {
	attr: InkAttrKeyword
}

#[derive(Clone, Debug)]
enum InkAttrKeyword {
	Storage,
	Message
}

impl syn::parse::Parse for InkAttrKeyword {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		if lookahead.peek(keywords::storage) {
			let _storage: keywords::storage = input.parse()?;
			return Ok(InkAttrKeyword::Storage)
		} else if lookahead.peek(keywords::message) {
			let _message: keywords::message = input.parse()?;
			return Ok(InkAttrKeyword::Message)
		} else {
			return Err(lookahead.error())
		}
	}
}

impl syn::parse::Parse for InkAttrs {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let mut attr = InkAttrKeyword::Storage;
		let args = Punctuated::<InkAttrKeyword, Token![,]>::parse_terminated(&input)?;
		println!("Args {:?}", args);
		for arg in args.into_iter() {
			match arg {
				InkAttrKeyword::Storage => {
					attr = InkAttrKeyword::Storage;
				},
				InkAttrKeyword::Message => {
					attr = InkAttrKeyword::Message;
				}
			}
		}
		Ok(InkAttrs { attr })
	}
}

#[derive(Clone)]
pub struct InkDef {
	pub attr_span: proc_macro2::Span,
	pub index: usize,
	pub ident: Option<syn::Ident>,
	pub vis: Option<syn::Visibility>,
	pub cfg_attrs: Vec<syn::Attribute>,
	pub where_clause: Option<syn::WhereClause>,
	pub docs: Vec<syn::Lit>,
    pub storage: bool
}

impl InkDef {
	pub fn prefix(&self) -> String {
		self.ident.clone().unwrap().to_string()
	}
	
    pub fn try_from(
		attr_tokens: Ident,
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
		dev_mode: bool,
	) -> syn::Result<Self> {
		let ink_args: InkAttrs = syn::parse(attr_tokens.to_token_stream().into())?;

		let vis;
		let ident;
		let cfg_attrs;
		let where_clause;
		let docs;
		let storage;

		match ink_args.attr {
			InkAttrKeyword::Storage => {
				let item = if let syn::Item::Struct(item) = item {
					item
				} else {
					return Err(syn::Error::new(item.span(), "Invalid pallet::ink, expect item struct."))
				};

				vis = Some(item.vis.clone());
				ident = Some(item.ident.clone());

				cfg_attrs = helper::get_item_cfg_attrs(&item.attrs);
				where_clause = item.generics.where_clause.clone();
				docs = get_doc_literals(&item.attrs);

				storage = true;
			},
			InkAttrKeyword::Message => {
				let item = if let syn::Item::Impl(item) = item {
					item
				} else {
					return Err(syn::Error::new(item.span(), "Invalid pallet::ink, expect item struct."))
				};

				vis = None; 
				ident = None;

				cfg_attrs = helper::get_item_cfg_attrs(&item.attrs);
				where_clause = None;
				docs = get_doc_literals(&item.attrs);

				storage = false;
			}
		}
		
        Ok(InkDef {
			attr_span,
			index,
			vis,
			ident,
			cfg_attrs,
			where_clause,
			docs,
            storage
        })
    }
}