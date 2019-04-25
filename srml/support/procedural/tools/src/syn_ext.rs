// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

use syn::parse::{
	Parse,
	ParseStream,
	Result,
};
use proc_macro2::TokenStream as T2;
use quote::{ToTokens, quote};
use std::iter::once;
use syn::Ident;
use srml_support_procedural_tools_derive::{ToTokens, Parse};

/// stop parsing here getting remaining token as content
/// Warn duplicate stream (part of)
#[derive(Parse, ToTokens, Debug)]
pub struct StopParse {
	pub inner: T2,
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
			fn to_tokens(&self, tokens: &mut T2) {
				let mut inner_stream = T2::new();
				self.content.to_tokens(&mut inner_stream);
				let token_tree: proc_macro2::TokenTree =
					proc_macro2::Group::new(proc_macro2::Delimiter::$deli, inner_stream).into();
				tokens.extend(once(token_tree));
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

#[derive(Debug)]
pub struct NoTrailing;


#[derive(Debug)]
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
	fn to_tokens(&self, tokens: &mut T2) {
		self.inner.to_tokens(tokens)
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
	fn to_tokens(&self, tokens: &mut T2) {
		match self.inner {
			syn::Meta::Word(ref ident) => {
				let ident = ident.clone();
				let toks = quote!{
					#[#ident]
				};
				tokens.extend(toks);
			},
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
	fn to_tokens(&self, tokens: &mut T2) {
		for att in self.inner.iter() {
			att.to_tokens(tokens);
		}
	}
}

#[derive(Debug)]
pub struct Opt<P> {
	pub inner: Option<P>,
}

impl<P: Parse> Parse for Opt<P> {
	// Note that it cost a double parsing (same as enum derive)
	fn parse(input: ParseStream) -> Result<Self> {
		let inner = match input.fork().parse::<P>() {
			Ok(_item) => Some(input.parse().expect("Same parsing ran before")),
			Err(_e) => None,
		};

		Ok(Opt { inner })
	}
}

impl<P: ToTokens> ToTokens for Opt<P> {
	fn to_tokens(&self, tokens: &mut T2) {
		if let Some(ref p) = self.inner {
			p.to_tokens(tokens);
		}
	}
}

pub fn extract_type_option(typ: &syn::Type) -> Option<T2> {
	if let syn::Type::Path(ref path) = typ {
		path.path.segments.last().and_then(|v| {
			if v.value().ident == "Option" {
				if let syn::PathArguments::AngleBracketed(ref a) = v.value().arguments {
					let args = &a.args;
					Some(quote!{ #args })
				} else {
					None
				}
			} else {
				None
			}
		})
	} else {
		None
	}
}

pub fn is_parametric_type_def(typ: &syn::Type, default: bool) -> bool {
	match *typ {
		syn::Type::Path(ref path) => {
			path.path.segments.iter().any(|v| {
				if let syn::PathArguments::AngleBracketed(..) = v.arguments {
					true
				} else {
					false
				}
			})
		},
		syn::Type::Slice(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::Array(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::Ptr(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::Reference(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::BareFn(ref inner) => inner.variadic.is_some(),
		syn::Type::Never(..) => false,
		syn::Type::Tuple(ref inner) =>
			inner.elems.iter().any(|t| is_parametric_type_def(t, default)),
		syn::Type::TraitObject(..) => true,
		syn::Type::ImplTrait(..) => true,
		syn::Type::Paren(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::Group(ref inner) => is_parametric_type_def(&inner.elem, default),
		syn::Type::Infer(..) => true,
		syn::Type::Macro(..) => default,
		syn::Type::Verbatim(..) => default,
	}
}

/// check if type has any type parameter, defaults to true for some cases.
pub fn is_parametric_type(typ: &syn::Type) -> bool {
	is_parametric_type_def(typ, true)
}

fn has_parametric_type_def_in_path(path: &syn::Path, ident: &Ident, default: bool) -> bool {
	path.segments.iter().any(|v| {
		if ident == &v.ident {
			return true;
		}
		if let syn::PathArguments::AngleBracketed(ref a) = v.arguments {
			for arg in a.args.iter() {
				if let syn::GenericArgument::Type(ref typ) = arg {
					if has_parametric_type_def(typ, ident, default) {
						return true;
					}
				}
				// potentially missing matches here
			}
			false
		} else {
			false
		}
	})

}
pub fn has_parametric_type_def(typ: &syn::Type, ident: &Ident, default: bool) -> bool {
	match *typ {
		syn::Type::Path(ref path) => has_parametric_type_def_in_path(&path.path, ident, default),
		syn::Type::Slice(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::Array(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::Ptr(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::Reference(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::BareFn(ref inner) => inner.variadic.is_some(),
		syn::Type::Never(..) => false,
		syn::Type::Tuple(ref inner) =>
			inner.elems.iter().any(|t| has_parametric_type_def(t, ident, default)),
		syn::Type::TraitObject(ref to) => {
			to.bounds.iter().any(|bound| {
				if let syn::TypeParamBound::Trait(ref t) = bound {
					has_parametric_type_def_in_path(&t.path, ident, default)
				} else { false }
			})
		},
		syn::Type::ImplTrait(ref it) => {
			it.bounds.iter().any(|bound| {
				if let syn::TypeParamBound::Trait(ref t) = bound {
					has_parametric_type_def_in_path(&t.path, ident, default)
				} else { false }
			})
		},
		syn::Type::Paren(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::Group(ref inner) => has_parametric_type_def(&inner.elem, ident, default),
		syn::Type::Infer(..) => default,
		syn::Type::Macro(..) => default,
		syn::Type::Verbatim(..) => default,
	}
}

/// check if type has a type parameter, defaults to true for some cases.
pub fn has_parametric_type(typ: &syn::Type, ident: &Ident) -> bool {
	has_parametric_type_def(typ, ident, true)
}
