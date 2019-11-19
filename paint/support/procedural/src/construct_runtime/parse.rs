// Copyright 2019 Parity Technologies (UK) Ltd.
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

use paint_support_procedural_tools::syn_ext as ext;
use proc_macro2::Span;
use std::collections::{BTreeMap, HashMap, HashSet};
use syn::{
    parse::{Parse, ParseStream},
    spanned::Spanned,
    token, Ident, Result, Token, Error
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
        let mut seen_keys = HashSet::new();
        let mut definitions = HashMap::new();
        while !input.peek(token::Brace) {
			let WhereDefinition { kind, value } = input.parse()?;
			if !seen_keys.insert(kind) {
				let msg = format!(
					"`{}` was declared above. Please use exactly one delcataion for `{}`.",
					kind, kind
				);
				return Err(Error::new(kind.span(), msg));
			}
            definitions.insert(kind, value);
            if !input.peek(Token![,]) {
                if !input.peek(token::Brace) {
                    return Err(input.error("Expected `,` or `{`"));
                }
                break;
            }
            input.parse::<Token![,]>()?;
        }
        let expected_seen_keys: HashSet<_> = vec![
            WhereKind::Block(Default::default()),
            WhereKind::NodeBlock(Default::default()),
            WhereKind::UncheckedExtrinsic(Default::default()),
        ]
        .into_iter()
        .collect();
        let diff: Vec<_> = expected_seen_keys.difference(&seen_keys).collect();
        if diff.len() > 0 {
            let msg = format!(
                "Missing associated type for `{:?}`. Add `{:?}` = ... to where section.",
                diff[0], diff[0]
            );
            return Err(input.error(msg));
        }
        Ok(Self {
            block: definitions
                .remove(&WhereKind::Block(Default::default()))
                .expect("Definitions is guaranteed to have this key; qed"),
            node_block: definitions
                .remove(&WhereKind::NodeBlock(Default::default()))
                .expect("Definitions is guaranteed to have this key; qed"),
            unchecked_extrinsic: definitions
                .remove(&WhereKind::UncheckedExtrinsic(Default::default()))
                .expect("Definitions is guaranteed to have this key; qed"),
        })
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum WhereKind {
    Block(keyword::Block),
    NodeBlock(keyword::NodeBlock),
    UncheckedExtrinsic(keyword::UncheckedExtrinsic),
}

impl std::cmp::PartialEq<WhereKind> for WhereKind {
	fn eq(&self, other: &WhereKind) -> bool {
		match (self, other) {
			(WhereKind::Block(_), WhereKind::Block(_)) => true,
			(WhereKind::NodeBlock(_), WhereKind::NodeBlock(_)) => true,
			(WhereKind::UncheckedExtrinsic(_), WhereKind::UncheckedExtrinsic(_)) => true,
			_ => false,
		}
	}
}

impl std::cmp::Eq for

impl std::hash::Hash for WhereKind {
    fn hash<H>(&self, state: &mut H)
    where
		H: std::hash::Hasher
	{
		state.write_u32(self as u32)
	}
}

impl std::fmt::Display for WhereKind {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		let name = match self {
			WhereKind::Block(_) => "Block",
			WhereKind::NodeBlock(_) => "NodeBlock",
			WhereKind::UncheckedExtrinsic(_) => "UncheckedExtrinsic",
		};
		write!(f, "{}", name)
	}
}

impl Parse for WhereKind {
    fn parse(input: ParseStream) -> Result<Self> {
        let lookahead = input.lookahead1();
        if lookahead.peek(keyword::Block) {
            WhereKind::Block(input.parse()?)
        } else if lookahead.peek(keyword::NodeBlock) {
            WhereKind::NodeBlock(input.parse()?)
        } else if lookahead.peek(keyword::UncheckedExtrinsic) {
			WhereKind::UncheckedExtrinsic(input.parse()?)
		} else {
            Err(lookahead.error())
        }
	}
}

impl WhereKind {
	pub fn span(&self) -> Span {
		match self {
			WhereKind::Block(x) => x.span(),
			WhereKind::NodeBlock(x) => x.span(),
			WhereKind::UncheckedExtrinsic(x) => x.span(),
		}
	}
}

#[derive(Debug)]
pub struct WhereDefinition {
    pub kind: WhereKind,
    pub value: syn::TypePath,
}

impl Parse for WhereDefinition {
    fn parse(input: ParseStream) -> Result<Self> {
		Ok(Self {
            kind: WhereKind::parse(input)?,
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
        Ok(Self {
            name,
            module,
            instance,
            details,
        })
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

#[derive(Debug, Clone)]
pub struct ModulePart {
    pub name: Ident,
    pub generics: syn::Generics,
    pub args: Option<ext::Parens<ext::Punctuated<Ident, Token![,]>>>,
}

impl Parse for ModulePart {
    fn parse(input: ParseStream) -> Result<Self> {
        let name = input.parse()?;
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

    pub fn allowed_generics() -> Vec<&'static str> {
        vec!["Event", "Origin", "Config"]
    }

    pub fn allowed_args() -> Vec<&'static str> {
        vec!["Inherent"]
    }

    pub fn format_names(names: Vec<&'static str>) -> String {
        let res: Vec<_> = names.into_iter().map(|s| format!("`{}`", s)).collect();
        res.join(", ")
    }
}

impl ModuleDeclaration {
    /// Get resolved module parts, i.e. after expanding `default` keyword
    /// or empty declaration
    pub fn module_parts(&self) -> Vec<ModulePart> {
        if let Some(ref details) = self.details {
            let uniq: BTreeMap<_, _> = details
                .content
                .inner
                .iter()
                .flat_map(|entry| match entry {
                    ModuleEntry::Default(ref token) => Self::default_modules(token.span()),
                    ModuleEntry::Part(ref part) => vec![part.clone()],
                })
                .map(|part| (part.name.to_string(), part))
                .collect();
            uniq.into_iter().map(|(_, v)| v).collect()
        } else {
            Self::default_modules(self.module.span())
        }
    }

    fn default_modules(span: Span) -> Vec<ModulePart> {
        let mut res: Vec<_> = ["Module", "Call", "Storage"]
            .into_iter()
            .map(|name| ModulePart::with_name(name, span))
            .collect();
        res.extend(
            ["Event", "Config"]
                .into_iter()
                .map(|name| ModulePart::with_generics(name, span)),
        );
        res
    }
}

impl ModulePart {
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
