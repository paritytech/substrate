// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

use frame_support_procedural_tools::syn_ext as ext;
use proc_macro2::Span;
use std::collections::HashSet;
use syn::{
	parse::{Parse, ParseStream},
	spanned::Spanned,
	token, Error, Ident, Result, Token,
};

mod keyword {
	syn::custom_keyword!(Block);
	syn::custom_keyword!(NodeBlock);
	syn::custom_keyword!(UncheckedExtrinsic);
}

#[derive(Debug)]
pub struct RuntimeDefinition {
	pub visibility_token: Token![pub],
	pub enum_token: Token![enum],
	pub name: Ident,
	pub where_section: WhereSection,
	pub modules: ext::Braces<ext::Punctuated<ModuleDeclaration, Token![,]>>,
}

impl Parse for RuntimeDefinition {
	fn parse(input: ParseStream) -> Result<Self> {
		Ok(Self {
			visibility_token: input.parse()?,
			enum_token: input.parse()?,
			name: input.parse()?,
			where_section: input.parse()?,
			modules: input.parse()?,
		})
	}
}

#[derive(Debug)]
pub struct WhereSection {
	pub block: syn::TypePath,
	pub node_block: syn::TypePath,
	pub unchecked_extrinsic: syn::TypePath,
}

impl Parse for WhereSection {
	fn parse(input: ParseStream) -> Result<Self> {
		input.parse::<token::Where>()?;
		let mut definitions = Vec::new();
		while !input.peek(token::Brace) {
			let definition: WhereDefinition = input.parse()?;
			definitions.push(definition);
			if !input.peek(Token![,]) {
				if !input.peek(token::Brace) {
					return Err(input.error("Expected `,` or `{`"));
				}
				break;
			}
			input.parse::<Token![,]>()?;
		}
		let block = remove_kind(input, WhereKind::Block, &mut definitions)?.value;
		let node_block = remove_kind(input, WhereKind::NodeBlock, &mut definitions)?.value;
		let unchecked_extrinsic =
			remove_kind(input, WhereKind::UncheckedExtrinsic, &mut definitions)?.value;
		if let Some(WhereDefinition {
			ref kind_span,
			ref kind,
			..
		}) = definitions.first()
		{
			let msg = format!(
				"`{:?}` was declared above. Please use exactly one delcataion for `{:?}`.",
				kind, kind
			);
			return Err(Error::new(*kind_span, msg));
		}
		Ok(Self {
			block,
			node_block,
			unchecked_extrinsic,
		})
	}
}

#[derive(Debug, PartialEq, Eq, Clone, Copy, Hash)]
pub enum WhereKind {
	Block,
	NodeBlock,
	UncheckedExtrinsic,
}

#[derive(Debug)]
pub struct WhereDefinition {
	pub kind_span: Span,
	pub kind: WhereKind,
	pub value: syn::TypePath,
}

impl Parse for WhereDefinition {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		let (kind_span, kind) = if lookahead.peek(keyword::Block) {
			(input.parse::<keyword::Block>()?.span(), WhereKind::Block)
		} else if lookahead.peek(keyword::NodeBlock) {
			(
				input.parse::<keyword::NodeBlock>()?.span(),
				WhereKind::NodeBlock,
			)
		} else if lookahead.peek(keyword::UncheckedExtrinsic) {
			(
				input.parse::<keyword::UncheckedExtrinsic>()?.span(),
				WhereKind::UncheckedExtrinsic,
			)
		} else {
			return Err(lookahead.error());
		};

		Ok(Self {
			kind_span,
			kind,
			value: {
				let _: Token![=] = input.parse()?;
				input.parse()?
			},
		})
	}
}

#[derive(Debug)]
pub struct ModuleDeclaration {
	pub name: Ident,
	pub module: Ident,
	pub instance: Option<Ident>,
	pub details: Option<ext::Braces<ext::Punctuated<ModuleEntry, Token![,]>>>,
}

impl Parse for ModuleDeclaration {
	fn parse(input: ParseStream) -> Result<Self> {
		let name = input.parse()?;
		let _: Token![:] = input.parse()?;
		let module = input.parse()?;
		let instance = if input.peek(Token![::]) && input.peek3(Token![<]) {
			let _: Token![::] = input.parse()?;
			let _: Token![<] = input.parse()?;
			let res = Some(input.parse()?);
			let _: Token![>] = input.parse()?;
			res
		} else {
			None
		};
		let details = if input.peek(Token![::]) {
			let _: Token![::] = input.parse()?;
			Some(input.parse()?)
		} else {
			None
		};
		let parsed = Self {
			name,
			module,
			instance,
			details,
		};
		if let Some(ref details) = parsed.details {
			let parts = &details.content.inner;
			let mut resolved = HashSet::new();
			let has_default = parts.into_iter().any(|m| m.is_default());
			for entry in parts {
				match entry {
					ModuleEntry::Part(part) => {
						if has_default && part.is_included_in_default() {
							let msg = format!(
									"`{}` is already included in `default`. Either remove `default` or remove `{}`",
									part.name,
									part.name
								);
							return Err(Error::new(part.name.span(), msg));
						}

						if !resolved.insert(part.name.clone()) {
							let msg = format!(
								"`{}` was already declared before. Please remove the duplicate declaration",
								part.name
							);
							return Err(Error::new(part.name.span(), msg));
						}
					}
					_ => {}
				}
			}
		}
		Ok(parsed)
	}
}

impl ModuleDeclaration {
	/// Get resolved module parts, i.e. after expanding `default` keyword
	/// or empty declaration
	pub fn module_parts(&self) -> Vec<ModulePart> {
		if let Some(ref details) = self.details {
			details
				.content
				.inner
				.iter()
				.flat_map(|entry| match entry {
					ModuleEntry::Default(ref token) => Self::default_modules(token.span()),
					ModuleEntry::Part(ref part) => vec![part.clone()],
				})
				.collect()
		} else {
			Self::default_modules(self.module.span())
		}
	}

	pub fn find_part(&self, name: &str) -> Option<ModulePart> {
		self.module_parts()
			.into_iter()
			.find(|part| part.name == name)
	}

	pub fn exists_part(&self, name: &str) -> bool {
		self.find_part(name).is_some()
	}

	fn default_modules(span: Span) -> Vec<ModulePart> {
		let mut res: Vec<_> = ["Module", "Call", "Storage"]
			.iter()
			.map(|name| ModulePart::with_name(name, span))
			.collect();
		res.extend(
			["Event", "Config"]
				.iter()
				.map(|name| ModulePart::with_generics(name, span)),
		);
		res
	}
}

#[derive(Debug)]
pub enum ModuleEntry {
	Default(Token![default]),
	Part(ModulePart),
}

impl Parse for ModuleEntry {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		if lookahead.peek(Token![default]) {
			Ok(ModuleEntry::Default(input.parse()?))
		} else if lookahead.peek(Ident) {
			Ok(ModuleEntry::Part(input.parse()?))
		} else {
			Err(lookahead.error())
		}
	}
}

impl ModuleEntry {
	pub fn is_default(&self) -> bool {
		match self {
			ModuleEntry::Default(_) => true,
			_ => false,
		}
	}
}

#[derive(Debug, Clone)]
pub struct ModulePart {
	pub name: Ident,
	pub generics: syn::Generics,
	pub args: Option<ext::Parens<ext::Punctuated<Ident, Token![,]>>>,
}

impl Parse for ModulePart {
	fn parse(input: ParseStream) -> Result<Self> {
		let name: Ident = input.parse()?;

		if !ModulePart::all_allowed().iter().any(|n| name == n) {
			return Err(syn::Error::new(
				name.span(),
				format!(
					"Only the following modules are allowed: {}",
					ModulePart::format_names(ModulePart::all_allowed()),
				),
			))
		}

		let generics: syn::Generics = input.parse()?;
		if !generics.params.is_empty() && !Self::is_allowed_generic(&name) {
			let valid_generics = ModulePart::format_names(ModulePart::allowed_generics());
			let msg = format!(
				"`{}` is not allowed to have generics. \
				 Only the following modules are allowed to have generics: {}.",
				name, valid_generics
			);
			return Err(syn::Error::new(name.span(), msg));
		}
		let args = if input.peek(token::Paren) {
			if !Self::is_allowed_arg(&name) {
				let syn::group::Parens { token: parens, .. } = syn::group::parse_parens(input)?;
				let valid_names = ModulePart::format_names(ModulePart::allowed_args());
				let msg = format!(
					"`{}` is not allowed to have arguments in parens. \
					 Only the following modules are allowed to have arguments in parens: {}.",
					name, valid_names
				);
				return Err(syn::Error::new(parens.span, msg));
			}
			Some(input.parse()?)
		} else {
			None
		};

		Ok(Self {
			name,
			generics,
			args,
		})
	}
}

impl ModulePart {
	pub fn is_allowed_generic(ident: &Ident) -> bool {
		Self::allowed_generics().into_iter().any(|n| ident == n)
	}

	pub fn is_allowed_arg(ident: &Ident) -> bool {
		Self::allowed_args().into_iter().any(|n| ident == n)
	}

	pub fn allowed_generics() -> &'static [&'static str] {
		&["Event", "Origin", "Config"]
	}

	pub fn allowed_args() -> &'static [&'static str] {
		&["Inherent"]
	}

	/// Returns all allowed names for module parts.
	pub fn all_allowed() -> &'static [&'static str] {
		&["Module", "Call", "Storage", "Event", "Config", "Origin", "Inherent", "ValidateUnsigned"]
	}

	pub fn format_names(names: &[&'static str]) -> String {
		let res: Vec<_> = names.into_iter().map(|s| format!("`{}`", s)).collect();
		res.join(", ")
	}

	pub fn is_included_in_default(&self) -> bool {
		["Module", "Call", "Storage", "Event", "Config"]
			.iter()
			.any(|name| self.name == name)
	}

	/// Plain module name like `Event` or `Call`, etc.
	pub fn with_name(name: &str, span: Span) -> Self {
		let name = Ident::new(name, span);
		Self {
			name,
			generics: syn::Generics {
				lt_token: None,
				gt_token: None,
				where_clause: None,
				..Default::default()
			},
			args: None,
		}
	}

	/// Module name with generic like `Event<T>` or `Call<T>`, etc.
	pub fn with_generics(name: &str, span: Span) -> Self {
		let name = Ident::new(name, span);
		let typ = Ident::new("T", span);
		let generic_param = syn::GenericParam::Type(typ.into());
		let generic_params = vec![generic_param].into_iter().collect();
		let generics = syn::Generics {
			lt_token: Some(syn::token::Lt { spans: [span] }),
			params: generic_params,
			gt_token: Some(syn::token::Gt { spans: [span] }),
			where_clause: None,
		};
		Self {
			name,
			generics,
			args: None,
		}
	}
}

fn remove_kind(
	input: ParseStream,
	kind: WhereKind,
	definitions: &mut Vec<WhereDefinition>,
) -> Result<WhereDefinition> {
	if let Some(pos) = definitions.iter().position(|d| d.kind == kind) {
		Ok(definitions.remove(pos))
	} else {
		let msg = format!(
			"Missing associated type for `{:?}`. Add `{:?}` = ... to where section.",
			kind, kind
		);
		Err(input.error(msg))
	}
}
