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
}

#[derive(Clone, Debug)]
struct InkAttrs {
	storage: bool,
}

enum InkAttrKeyword {
	Storage,
}

impl syn::parse::Parse for InkAttrKeyword {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		if lookahead.peek(keywords::storage) {
			let _storage: keywords::storage = input.parse()?;
			return Ok(InkAttrKeyword::Storage)
		} else {
			return Err(lookahead.error())
		}
	}
}

impl syn::parse::Parse for InkAttrs {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let mut storage = false;
		let args = Punctuated::<InkAttrKeyword, Token![,]>::parse_terminated(&input)?;
		for arg in args.into_iter() {
			match arg {
				InkAttrKeyword::Storage => {
					storage = true;
				},
			}
		}
		Ok(InkAttrs { storage })
	}
}

#[derive(Clone)]
pub struct InkDef {
	pub index: usize,
    storage: bool
}

impl InkDef {
    pub fn try_from(
		attr_tokens: Ident,
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
		dev_mode: bool,
	) -> syn::Result<Self> {
		let ink_args: InkAttrs = syn::parse(attr_tokens.to_token_stream().into())?;
		
        Ok(InkDef {
			index,
            storage: ink_args.storage
        })
    }
}