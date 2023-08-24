// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use super::helper;
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use syn::{spanned::Spanned, token, Token};

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(Config);
	syn::custom_keyword!(From);
	syn::custom_keyword!(T);
	syn::custom_keyword!(I);
	syn::custom_keyword!(config);
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(IsType);
	syn::custom_keyword!(RuntimeEvent);
	syn::custom_keyword!(Event);
	syn::custom_keyword!(frame_system);
	syn::custom_keyword!(disable_frame_system_supertrait_check);
	syn::custom_keyword!(no_default);
	syn::custom_keyword!(constant);
}

#[derive(Default)]
pub struct DefaultTrait {
	pub items: Vec<syn::TraitItem>,
	pub has_system: bool,
}

/// Input definition for the pallet config.
pub struct ConfigDef {
	/// The index of item in pallet module.
	pub index: usize,
	/// Whether the trait has instance (i.e. define with `Config<I = ()>`)
	pub has_instance: bool,
	/// Const associated type.
	pub consts_metadata: Vec<ConstMetadataDef>,
	/// Whether the trait has the associated type `Event`, note that those bounds are
	/// checked:
	/// * `IsType<Self as frame_system::Config>::RuntimeEvent`
	/// * `From<Event>` or `From<Event<T>>` or `From<Event<T, I>>`
	pub has_event_type: bool,
	/// The where clause on trait definition but modified so `Self` is `T`.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::config attribute.
	pub attr_span: proc_macro2::Span,
	/// Whether a default sub-trait should be generated.
	///
	/// Contains default sub-trait items (instantiated by `#[pallet::config(with_default)]`).
	/// Vec will be empty if `#[pallet::config(with_default)]` is not specified or if there are
	/// no trait items.
	pub default_sub_trait: Option<DefaultTrait>,
}

/// Input definition for a constant in pallet config.
pub struct ConstMetadataDef {
	/// Name of the associated type.
	pub ident: syn::Ident,
	/// The type in Get, e.g. `u32` in `type Foo: Get<u32>;`, but `Self` is replaced by `T`
	pub type_: syn::Type,
	/// The doc associated
	pub doc: Vec<syn::Expr>,
}

impl TryFrom<&syn::TraitItemType> for ConstMetadataDef {
	type Error = syn::Error;

	fn try_from(trait_ty: &syn::TraitItemType) -> Result<Self, Self::Error> {
		let err = |span, msg| {
			syn::Error::new(span, format!("Invalid usage of `#[pallet::constant]`: {}", msg))
		};
		let doc = get_doc_literals(&trait_ty.attrs);
		let ident = trait_ty.ident.clone();
		let bound = trait_ty
			.bounds
			.iter()
			.find_map(|b| {
				if let syn::TypeParamBound::Trait(tb) = b {
					tb.path
						.segments
						.last()
						.and_then(|s| if s.ident == "Get" { Some(s) } else { None })
				} else {
					None
				}
			})
			.ok_or_else(|| err(trait_ty.span(), "`Get<T>` trait bound not found"))?;
		let type_arg = if let syn::PathArguments::AngleBracketed(ref ab) = bound.arguments {
			if ab.args.len() == 1 {
				if let syn::GenericArgument::Type(ref ty) = ab.args[0] {
					Ok(ty)
				} else {
					Err(err(ab.args[0].span(), "Expected a type argument"))
				}
			} else {
				Err(err(bound.span(), "Expected a single type argument"))
			}
		} else {
			Err(err(bound.span(), "Expected trait generic args"))
		}?;
		let type_ = syn::parse2::<syn::Type>(replace_self_by_t(type_arg.to_token_stream()))
			.expect("Internal error: replacing `Self` by `T` should result in valid type");

		Ok(Self { ident, type_, doc })
	}
}

/// Parse for `#[pallet::disable_frame_system_supertrait_check]`
pub struct DisableFrameSystemSupertraitCheck;

impl syn::parse::Parse for DisableFrameSystemSupertraitCheck {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<syn::Ident>()?;
		content.parse::<syn::Token![::]>()?;

		content.parse::<keyword::disable_frame_system_supertrait_check>()?;
		Ok(Self)
	}
}

/// Parsing for the `typ` portion of `PalletAttr`
#[derive(derive_syn_parse::Parse, PartialEq, Eq)]
pub enum PalletAttrType {
	#[peek(keyword::no_default, name = "no_default")]
	NoDefault(keyword::no_default),
	#[peek(keyword::constant, name = "constant")]
	Constant(keyword::constant),
}

/// Parsing for `#[pallet::X]`
#[derive(derive_syn_parse::Parse)]
pub struct PalletAttr {
	_pound: Token![#],
	#[bracket]
	_bracket: token::Bracket,
	#[inside(_bracket)]
	_pallet: keyword::pallet,
	#[prefix(Token![::] in _bracket)]
	#[inside(_bracket)]
	typ: PalletAttrType,
}

pub struct ConfigBoundParse(syn::Ident);

impl syn::parse::Parse for ConfigBoundParse {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let ident = input.parse::<syn::Ident>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::Config>()?;

		if input.peek(syn::token::Lt) {
			input.parse::<syn::AngleBracketedGenericArguments>()?;
		}

		Ok(Self(ident))
	}
}

/// Parse for `IsType<<Sef as $ident::Config>::RuntimeEvent>` and retrieve `$ident`
pub struct IsTypeBoundEventParse(syn::Ident);

impl syn::parse::Parse for IsTypeBoundEventParse {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<keyword::IsType>()?;
		input.parse::<syn::Token![<]>()?;
		input.parse::<syn::Token![<]>()?;
		input.parse::<syn::Token![Self]>()?;
		input.parse::<syn::Token![as]>()?;
		let ident = input.parse::<syn::Ident>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::Config>()?;
		input.parse::<syn::Token![>]>()?;
		input.parse::<syn::Token![::]>()?;
		input.parse::<keyword::RuntimeEvent>()?;
		input.parse::<syn::Token![>]>()?;

		Ok(Self(ident))
	}
}

/// Parse for `From<Event>` or `From<Event<Self>>` or `From<Event<Self, I>>`
pub struct FromEventParse {
	is_generic: bool,
	has_instance: bool,
}

impl syn::parse::Parse for FromEventParse {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		let mut is_generic = false;
		let mut has_instance = false;

		input.parse::<keyword::From>()?;
		input.parse::<syn::Token![<]>()?;
		input.parse::<keyword::Event>()?;
		if input.peek(syn::Token![<]) {
			is_generic = true;
			input.parse::<syn::Token![<]>()?;
			input.parse::<syn::Token![Self]>()?;
			if input.peek(syn::Token![,]) {
				input.parse::<syn::Token![,]>()?;
				input.parse::<keyword::I>()?;
				has_instance = true;
			}
			input.parse::<syn::Token![>]>()?;
		}
		input.parse::<syn::Token![>]>()?;

		Ok(Self { is_generic, has_instance })
	}
}

/// Check if trait_item is `type RuntimeEvent`, if so checks its bounds are those expected.
/// (Event type is reserved type)
fn check_event_type(
	frame_system: &syn::Ident,
	trait_item: &syn::TraitItem,
	trait_has_instance: bool,
) -> syn::Result<bool> {
	if let syn::TraitItem::Type(type_) = trait_item {
		if type_.ident == "RuntimeEvent" {
			// Check event has no generics
			if !type_.generics.params.is_empty() || type_.generics.where_clause.is_some() {
				let msg = "Invalid `type RuntimeEvent`, associated type `RuntimeEvent` is reserved and must have\
					no generics nor where_clause";
				return Err(syn::Error::new(trait_item.span(), msg))
			}
			// Check bound contains IsType and From

			let has_is_type_bound = type_.bounds.iter().any(|s| {
				syn::parse2::<IsTypeBoundEventParse>(s.to_token_stream())
					.map_or(false, |b| b.0 == *frame_system)
			});

			if !has_is_type_bound {
				let msg = format!(
					"Invalid `type RuntimeEvent`, associated type `RuntimeEvent` is reserved and must \
					bound: `IsType<<Self as {}::Config>::RuntimeEvent>`",
					frame_system,
				);
				return Err(syn::Error::new(type_.span(), msg))
			}

			let from_event_bound = type_
				.bounds
				.iter()
				.find_map(|s| syn::parse2::<FromEventParse>(s.to_token_stream()).ok());

			let from_event_bound = if let Some(b) = from_event_bound {
				b
			} else {
				let msg = "Invalid `type RuntimeEvent`, associated type `RuntimeEvent` is reserved and must \
					bound: `From<Event>` or `From<Event<Self>>` or `From<Event<Self, I>>`";
				return Err(syn::Error::new(type_.span(), msg))
			};

			if from_event_bound.is_generic && (from_event_bound.has_instance != trait_has_instance)
			{
				let msg = "Invalid `type RuntimeEvent`, associated type `RuntimeEvent` bounds inconsistent \
					`From<Event..>`. Config and generic Event must be both with instance or \
					without instance";
				return Err(syn::Error::new(type_.span(), msg))
			}

			Ok(true)
		} else {
			Ok(false)
		}
	} else {
		Ok(false)
	}
}

/// Replace ident `Self` by `T`
pub fn replace_self_by_t(input: proc_macro2::TokenStream) -> proc_macro2::TokenStream {
	input
		.into_iter()
		.map(|token_tree| match token_tree {
			proc_macro2::TokenTree::Group(group) =>
				proc_macro2::Group::new(group.delimiter(), replace_self_by_t(group.stream())).into(),
			proc_macro2::TokenTree::Ident(ident) if ident == "Self" =>
				proc_macro2::Ident::new("T", ident.span()).into(),
			other => other,
		})
		.collect()
}

impl ConfigDef {
	pub fn try_from(
		frame_system: &syn::Ident,
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
		enable_default: bool,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Trait(item) = item {
			item
		} else {
			let msg = "Invalid pallet::config, expected trait definition";
			return Err(syn::Error::new(item.span(), msg))
		};

		if !matches!(item.vis, syn::Visibility::Public(_)) {
			let msg = "Invalid pallet::config, trait must be public";
			return Err(syn::Error::new(item.span(), msg))
		}

		syn::parse2::<keyword::Config>(item.ident.to_token_stream())?;

		let where_clause = {
			let stream = replace_self_by_t(item.generics.where_clause.to_token_stream());
			syn::parse2::<Option<syn::WhereClause>>(stream).expect(
				"Internal error: replacing `Self` by `T` should result in valid where
					clause",
			)
		};

		if item.generics.params.len() > 1 {
			let msg = "Invalid pallet::config, expected no more than one generic";
			return Err(syn::Error::new(item.generics.params[2].span(), msg))
		}

		let has_instance = if item.generics.params.first().is_some() {
			helper::check_config_def_gen(&item.generics, item.ident.span())?;
			true
		} else {
			false
		};

		let has_frame_system_supertrait = item.supertraits.iter().any(|s| {
			syn::parse2::<ConfigBoundParse>(s.to_token_stream())
				.map_or(false, |b| b.0 == *frame_system)
		});

		let mut has_event_type = false;
		let mut consts_metadata = vec![];
		let mut default_sub_trait = if enable_default {
			Some(DefaultTrait {
				items: Default::default(),
				has_system: has_frame_system_supertrait,
			})
		} else {
			None
		};
		for trait_item in &mut item.items {
			let is_event = check_event_type(frame_system, trait_item, has_instance)?;
			has_event_type = has_event_type || is_event;

			let mut already_no_default = false;
			let mut already_constant = false;

			while let Ok(Some(pallet_attr)) =
				helper::take_first_item_pallet_attr::<PalletAttr>(trait_item)
			{
				match (pallet_attr.typ, &trait_item) {
					(PalletAttrType::Constant(_), syn::TraitItem::Type(ref typ)) => {
						if already_constant {
							return Err(syn::Error::new(
								pallet_attr._bracket.span.join(),
								"Duplicate #[pallet::constant] attribute not allowed.",
							))
						}
						already_constant = true;
						consts_metadata.push(ConstMetadataDef::try_from(typ)?);
					},
					(PalletAttrType::Constant(_), _) =>
						return Err(syn::Error::new(
							trait_item.span(),
							"Invalid #[pallet::constant] in #[pallet::config], expected type item",
						)),
					(PalletAttrType::NoDefault(_), _) => {
						if !enable_default {
							return Err(syn::Error::new(
								pallet_attr._bracket.span.join(),
								"`#[pallet:no_default]` can only be used if `#[pallet::config(with_default)]` \
								has been specified"
							))
						}
						if already_no_default {
							return Err(syn::Error::new(
								pallet_attr._bracket.span.join(),
								"Duplicate #[pallet::no_default] attribute not allowed.",
							))
						}

						already_no_default = true;
					},
				}
			}

			if !already_no_default && !is_event && enable_default {
				default_sub_trait
					.as_mut()
					.expect("is 'Some(_)' if 'enable_default'; qed")
					.items
					.push(trait_item.clone());
			}
		}

		let attr: Option<DisableFrameSystemSupertraitCheck> =
			helper::take_first_item_pallet_attr(&mut item.attrs)?;
		let disable_system_supertrait_check = attr.is_some();

		if !has_frame_system_supertrait && !disable_system_supertrait_check {
			let found = if item.supertraits.is_empty() {
				"none".to_string()
			} else {
				let mut found = item
					.supertraits
					.iter()
					.fold(String::new(), |acc, s| format!("{}`{}`, ", acc, quote::quote!(#s)));
				found.pop();
				found.pop();
				found
			};

			let msg = format!(
				"Invalid pallet::trait, expected explicit `{}::Config` as supertrait, \
				found {}. \
				(try `pub trait Config: frame_system::Config {{ ...` or \
				`pub trait Config<I: 'static>: frame_system::Config {{ ...`). \
				To disable this check, use `#[pallet::disable_frame_system_supertrait_check]`",
				frame_system, found,
			);
			return Err(syn::Error::new(item.span(), msg))
		}

		Ok(Self {
			index,
			has_instance,
			consts_metadata,
			has_event_type,
			where_clause,
			attr_span,
			default_sub_trait,
		})
	}
}
