// Copyright 2017-2020 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

// tag::description[]
//! Extension to syn types, mainly for parsing
// end::description[]

use syn::{visit::{Visit, self}, parse::{Parse, ParseStream, Result}, Ident};
use proc_macro2::{TokenStream, TokenTree};
use quote::ToTokens;
use std::iter::once;
use frame_support_procedural_tools_derive::{ToTokens, Parse};

/// stop parsing here getting remaining token as content
/// Warn duplicate stream (part of)
#[derive(Parse, ToTokens, Debug)]
pub struct StopParse {
	pub inner: TokenStream,
}

// inner macro really dependant on syn naming convention, do not export
macro_rules! groups_impl {
	($name:ident, $tok:ident, $deli:ident, $parse:ident) => {

		#[derive(Debug)]
		pub struct $name<P> {
			pub token: syn::token::$tok,
			pub content: P,
		}

		impl<P: Parse> Parse for $name<P> {
			fn parse(input: ParseStream) -> Result<Self> {
				let syn::group::$name { token, content } = syn::group::$parse(input)?;
				let content = content.parse()?;
				Ok($name { token, content, })
			}
		}

		impl<P: ToTokens> ToTokens for $name<P> {
			fn to_tokens(&self, tokens: &mut TokenStream) {
				let mut inner_stream = TokenStream::new();
				self.content.to_tokens(&mut inner_stream);
				let token_tree: proc_macro2::TokenTree =
					proc_macro2::Group::new(proc_macro2::Delimiter::$deli, inner_stream).into();
				tokens.extend(once(token_tree));
			}
		}

		impl <P: Clone> Clone for $name<P> {
			fn clone(&self) -> Self {
				Self { token: self.token.clone(), content: self.content.clone() }
			}
		}
	}
}

groups_impl!(Braces, Brace, Brace, parse_braces);
groups_impl!(Brackets, Bracket, Bracket, parse_brackets);
groups_impl!(Parens, Paren, Parenthesis, parse_parens);

#[derive(Debug)]
pub struct PunctuatedInner<P,T,V> {
	pub inner: syn::punctuated::Punctuated<P,T>,
	pub variant: V,
}

#[derive(Debug, Clone)]
pub struct NoTrailing;


#[derive(Debug, Clone)]
pub struct Trailing;

pub type Punctuated<P,T> = PunctuatedInner<P,T,NoTrailing>;

pub type PunctuatedTrailing<P,T> = PunctuatedInner<P,T,Trailing>;

impl<P: Parse, T: Parse + syn::token::Token> Parse for PunctuatedInner<P,T,Trailing> {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(PunctuatedInner {
			inner: syn::punctuated::Punctuated::parse_separated_nonempty(input)?,
			variant: Trailing,
		})
	}
}

impl<P: Parse, T: Parse> Parse for PunctuatedInner<P,T,NoTrailing> {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(PunctuatedInner {
			inner: syn::punctuated::Punctuated::parse_terminated(input)?,
			variant: NoTrailing,
		})
	}
}

impl<P: ToTokens, T: ToTokens, V> ToTokens for PunctuatedInner<P,T,V> {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		self.inner.to_tokens(tokens)
	}
}

impl <P: Clone, T: Clone, V: Clone> Clone for PunctuatedInner<P, T, V> {
	fn clone(&self) -> Self {
		Self { inner: self.inner.clone(), variant: self.variant.clone() }
	}
}

/// Note that syn Meta is almost fine for use case (lacks only `ToToken`)
#[derive(Debug, Clone)]
pub struct Meta {
	pub inner: syn::Meta,
}

impl Parse for Meta {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(Meta {
			inner: syn::Meta::parse(input)?,
		})
	}
}

impl ToTokens for Meta {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		match self.inner {
			syn::Meta::Path(ref path) => path.to_tokens(tokens),
			syn::Meta::List(ref l) => l.to_tokens(tokens),
			syn::Meta::NameValue(ref n) => n.to_tokens(tokens),
		}
	}
}

#[derive(Debug)]
pub struct OuterAttributes {
	pub inner: Vec<syn::Attribute>,
}

impl Parse for OuterAttributes {
	fn parse(input: ParseStream) -> Result<Self> {
		let inner = syn::Attribute::parse_outer(input)?;
		Ok(OuterAttributes {
			inner,
		})
	}
}

impl ToTokens for OuterAttributes {
	fn to_tokens(&self, tokens: &mut TokenStream) {
		for att in self.inner.iter() {
			att.to_tokens(tokens);
		}
	}
}

pub fn extract_type_option(typ: &syn::Type) -> Option<syn::Type> {
	if let syn::Type::Path(ref path) = typ {
		let v = path.path.segments.last()?;
		if v.ident == "Option" {
			// Option has only one type argument in angle bracket.
			if let syn::PathArguments::AngleBracketed(a) = &v.arguments {
				if let syn::GenericArgument::Type(typ) = a.args.last()? {
					return Some(typ.clone())
				}
			}
		}
	}

	None
}

/// Auxiliary structure to check if a given `Ident` is contained in an ast.
struct ContainsIdent<'a> {
	ident: &'a Ident,
	result: bool,
}

impl<'ast> ContainsIdent<'ast> {
	fn visit_tokenstream(&mut self, stream: TokenStream) {
		stream.into_iter().for_each(|tt|
			match tt {
				TokenTree::Ident(id) => self.visit_ident(&id),
				TokenTree::Group(ref group) => self.visit_tokenstream(group.stream()),
				_ => {}
			}
		)
	}

	fn visit_ident(&mut self, ident: &Ident) {
		if ident == self.ident {
			self.result = true;
		}
	}
}

impl<'ast> Visit<'ast> for ContainsIdent<'ast> {
	fn visit_ident(&mut self, input: &'ast Ident) {
		self.visit_ident(input);
	}

	fn visit_macro(&mut self, input: &'ast syn::Macro) {
		self.visit_tokenstream(input.tokens.clone());
		visit::visit_macro(self, input);
	}
}

/// Check if a `Type` contains the given `Ident`.
pub fn type_contains_ident(typ: &syn::Type, ident: &Ident) -> bool {
	let mut visit = ContainsIdent {
		result: false,
		ident,
	};

	visit::visit_type(&mut visit, typ);
	visit.result
}

/// Check if a `Expr` contains the given `Ident`.
pub fn expr_contains_ident(expr: &syn::Expr, ident: &Ident) -> bool {
	let mut visit = ContainsIdent {
		result: false,
		ident,
	};

	visit::visit_expr(&mut visit, expr);
	visit.result
}
