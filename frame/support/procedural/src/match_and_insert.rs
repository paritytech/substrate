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

//! Implementation of the `match_and_insert` macro.

use proc_macro2::{Group, Span, TokenStream, TokenTree};
use std::iter::once;
use syn::spanned::Spanned;

mod keyword {
	syn::custom_keyword!(target);
	syn::custom_keyword!(pattern);
	syn::custom_keyword!(tokens);
}

pub fn match_and_insert(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	let MatchAndInsertDef { pattern, tokens, target } =
		syn::parse_macro_input!(input as MatchAndInsertDef);

	match expand_in_stream(&pattern, &mut Some(tokens), target) {
		Ok(stream) => stream.into(),
		Err(err) => err.to_compile_error().into(),
	}
}

struct MatchAndInsertDef {
	// Token stream to search and insert tokens into.
	target: TokenStream,
	// Pattern to match against, this is ensured to have no TokenTree::Group nor TokenTree::Literal
	// (i.e. contains only Punct or Ident), and not being empty.
	pattern: Vec<TokenTree>,
	// Token stream to insert after the match pattern.
	tokens: TokenStream,
}

impl syn::parse::Parse for MatchAndInsertDef {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let mut target;
		let _ = input.parse::<keyword::target>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(target in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(target in target);
		let target = target.parse()?;

		let mut pattern;
		let _ = input.parse::<keyword::pattern>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(pattern in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(pattern in pattern);
		let pattern = pattern.parse::<TokenStream>()?.into_iter().collect::<Vec<TokenTree>>();

		if let Some(t) = pattern.iter().find(|t| matches!(t, TokenTree::Group(_))) {
			return Err(syn::Error::new(t.span(), "Unexpected group token tree"))
		}
		if let Some(t) = pattern.iter().find(|t| matches!(t, TokenTree::Literal(_))) {
			return Err(syn::Error::new(t.span(), "Unexpected literal token tree"))
		}

		if pattern.is_empty() {
			return Err(syn::Error::new(Span::call_site(), "empty match pattern is invalid"))
		}

		let mut tokens;
		let _ = input.parse::<keyword::tokens>()?;
		let _ = input.parse::<syn::Token![=]>()?;
		let _replace_with_bracket: syn::token::Bracket = syn::bracketed!(tokens in input);
		let _replace_with_brace: syn::token::Brace = syn::braced!(tokens in tokens);
		let tokens = tokens.parse()?;

		Ok(Self { tokens, pattern, target })
	}
}

// Insert `tokens` after the first matching `pattern`.
// `tokens` must be some (Option is used for internal simplification).
// `pattern` must not be empty and should only contain Ident or Punct.
fn expand_in_stream(
	pattern: &[TokenTree],
	tokens: &mut Option<TokenStream>,
	stream: TokenStream,
) -> syn::Result<TokenStream> {
	assert!(
		tokens.is_some(),
		"`tokens` must be some, Option is used because `tokens` is used only once"
	);
	assert!(
		!pattern.is_empty(),
		"`pattern` must not be empty, otherwise there is nothing to match against"
	);

	let stream_span = stream.span();
	let mut stream = stream.into_iter();
	let mut extended = TokenStream::new();
	let mut match_cursor = 0;

	while let Some(token) = stream.next() {
		match token {
			TokenTree::Group(group) => {
				match_cursor = 0;
				let group_stream = group.stream();
				match expand_in_stream(pattern, tokens, group_stream) {
					Ok(s) => {
						extended.extend(once(TokenTree::Group(Group::new(group.delimiter(), s))));
						extended.extend(stream);
						return Ok(extended)
					},
					Err(_) => {
						extended.extend(once(TokenTree::Group(group)));
					},
				}
			},
			other => {
				advance_match_cursor(&other, pattern, &mut match_cursor);

				extended.extend(once(other));

				if match_cursor == pattern.len() {
					extended
						.extend(once(tokens.take().expect("tokens is used to replace only once")));
					extended.extend(stream);
					return Ok(extended)
				}
			},
		}
	}
	// if we reach this point, it means the stream is empty and we haven't found a matching pattern
	let msg = format!("Cannot find pattern `{:?}` in given token stream", pattern);
	Err(syn::Error::new(stream_span, msg))
}

fn advance_match_cursor(other: &TokenTree, pattern: &[TokenTree], match_cursor: &mut usize) {
	use TokenTree::{Ident, Punct};

	let does_match_other_pattern = match (other, &pattern[*match_cursor]) {
		(Ident(i1), Ident(i2)) => i1 == i2,
		(Punct(p1), Punct(p2)) => p1.as_char() == p2.as_char(),
		_ => false,
	};

	if does_match_other_pattern {
		*match_cursor += 1;
	} else {
		*match_cursor = 0;
	}
}
