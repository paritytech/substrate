// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Implementation of macro `expand_after`.

use proc_macro2::{Group, Span, TokenStream, TokenTree};
use std::iter::once;
use syn::spanned::Spanned;

pub fn expand_after(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let def = syn::parse_macro_input!(input as ExpandAfterDef);

	match expand_in_stream(&def.expand_after, &mut Some(def.expand_with), def.expand_in) {
		Ok(stream) => stream.into(),
		Err(err) => err.to_compile_error().into(),
	}
}

struct ExpandAfterDef {
	// Pattern to expand after, this is ensured to have no TokenTree::Group nor TokenTree::Literal
	// (i.e. contains only Punct or Ident), and not being empty.
	expand_after: Vec<TokenTree>,
	// Token stream to write after match.
	expand_with: TokenStream,
	// Token stream to search and write inside.
	expand_in: TokenStream,
}

impl syn::parse::Parse for ExpandAfterDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let expand_after;
		let _replace_with_bracket: syn::token::Brace = syn::braced!(expand_after in input);
		let expand_after =
			expand_after.parse::<TokenStream>()?.into_iter().collect::<Vec<TokenTree>>();

		if let Some(t) = expand_after.iter().find(|t| matches!(t, TokenTree::Group(_))) {
			return Err(syn::Error::new(t.span(), "Unexpected group token tree"))
		}
		if let Some(t) = expand_after.iter().find(|t| matches!(t, TokenTree::Literal(_))) {
			return Err(syn::Error::new(t.span(), "Unexpected literal token tree"))
		}

		if expand_after.is_empty() {
			return Err(syn::Error::new(Span::call_site(), "empty match pattern is invalid"))
		}

		let expand_with;
		let _replace_with_bracket: syn::token::Brace = syn::braced!(expand_with in input);
		let expand_with: TokenStream = expand_with.parse()?;

		Ok(Self { expand_with, expand_after, expand_in: input.parse()? })
	}
}

// Replace the first found `after` pattern by content of `with`.
// `with` must be some (Option is used for internal simplification).
// `after` musn't be empty and only contains Ident or Punct
fn expand_in_stream(
	after: &[TokenTree],
	with: &mut Option<TokenStream>,
	stream: TokenStream,
) -> syn::Result<TokenStream> {
	assert!(with.is_some(), "`with` must be some, Option is used because `with` is used only once");
	assert!(!after.is_empty(), "`after` mustn't be empty, otherwise it cannot be found");

	let stream_span = stream.span();
	let mut stream = stream.into_iter();
	let mut extended = TokenStream::new();
	let mut match_cursor = 0;

	while let Some(token) = stream.next() {
		match token {
			TokenTree::Group(group) => {
				match_cursor = 0;
				let group_stream = group.stream();
				match expand_in_stream(after, with, group_stream) {
					Ok(s) => {
						extended
							.extend(once(TokenTree::Group(Group::new(group.delimiter(), s))));
						extended.extend(stream);
						return Ok(extended)
					},
					Err(_) => {
						extended.extend(once(TokenTree::Group(group)));
					},
				}
			},
			other => {
				advance_match_cursor(&other, after, &mut match_cursor);

				extended.extend(once(other));

				if match_cursor == after.len() {
					extended.extend(once(with.take().expect("with is used to replace only once")));
					extended.extend(stream);
					return Ok(extended)
				}
			},
		}
	}
	// if we reach this point, it means the stream is empty and we haven't found a matching pattern
	let msg = format!("Cannot find pattern `{:?}` in given token stream", after);
	Err(syn::Error::new(stream_span, msg))
}

fn advance_match_cursor(other: &TokenTree, after: &[TokenTree], match_cursor: &mut usize) {
	use TokenTree::{Ident, Punct};

	let other_match_pattern = match (other, &after[*match_cursor]) {
		(Ident(i1), Ident(i2)) => i1 == i2,
		(Punct(p1), Punct(p2)) => p1.as_char() == p2.as_char(),
		_ => false,
	};

	if other_match_pattern {
		*match_cursor += 1;
	}
}
