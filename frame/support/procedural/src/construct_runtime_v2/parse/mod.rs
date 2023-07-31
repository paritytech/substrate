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

pub mod runtime_struct;
pub mod pallets;
pub mod helper;

use syn::spanned::Spanned;
use syn::Result;
use quote::ToTokens;

use self::pallets::AllPalletsDeclaration;
use crate::construct_runtime::check_pallet_number;
use crate::construct_runtime_v2::parse::pallets::{ImplicitAllPalletsDeclaration, ExplicitAllPalletsDeclaration};
use frame_support_procedural_tools::{
	generate_crate_access, generate_crate_access_2018, generate_hidden_includes,
};
use proc_macro2::TokenStream as TokenStream2;

pub struct Def {
    pub item: syn::ItemMod,
    pub runtime_struct: runtime_struct::RuntimeStructDef,
	pub pallets: (pallets::AllPalletsDeclaration, TokenStream2),
}

impl Def {
	pub fn try_from(mut item: syn::ItemMod) -> syn::Result<Self> {
		let input_main: TokenStream2 = item.to_token_stream().into();
		// println!("input_main: {}", input_main);
        let item_span = item.span();
		let items = &mut item
			.content
			.as_mut()
			.ok_or_else(|| {
				let msg = "Invalid runtime definition, expected mod to be inlined.";
				syn::Error::new(item_span, msg)
			})?
			.1;

        let mut runtime_struct = None;
		let mut pallets = None;

        for (index, item) in items.iter_mut().enumerate() {
            let runtime_attr: Option<RuntimeAttr> = helper::take_first_item_runtime_attr(item)?;

            match runtime_attr {
				Some(RuntimeAttr::Runtime(span)) if runtime_struct.is_none() => {
					let p = runtime_struct::RuntimeStructDef::try_from(span, index, item)?;
					runtime_struct = Some(p);
				},
				Some(RuntimeAttr::Pallets(span)) if pallets.is_none() => {
					let input: TokenStream2 = item.to_token_stream().into();
					let input_copy = input_main.clone();
					let definition = syn::parse2::<pallets::AllPalletsDeclaration>(input)?;
					let res = match definition.clone() {
						AllPalletsDeclaration::Implicit(implicit_def) =>
							check_pallet_number(input_copy.clone().into(), implicit_def.pallets.len()).and_then(
								|_| construct_runtime_implicit_to_explicit(input_copy.into(), implicit_def),
							),
						AllPalletsDeclaration::Explicit(explicit_decl) => check_pallet_number(
							input_copy.clone().into(),
							explicit_decl.pallets.len(),
						).and_then(|_| {
							construct_runtime_explicit_to_explicit_expanded(input_copy.into(), explicit_decl)
						}),
						AllPalletsDeclaration::ExplicitExpanded(explicit_decl) =>
							check_pallet_number(input_copy.clone().into(), explicit_decl.pallets.len())
								.and_then(|_| Ok(input_copy)),
					}?;	
					// println!("definition: {:?}", definition);
					// println!("res: {}", res);
					// let p = syn::parse2::<pallets::AllPalletsDeclaration>(res)?;			
					pallets = Some((definition, res));
				},
                Some(attr) => {
					let msg = "Invalid duplicated attribute";
					return Err(syn::Error::new(attr.span(), msg))
				},
                None => (),
			}
        }

        let def = Def {
			item,
			runtime_struct: runtime_struct
				.ok_or_else(|| syn::Error::new(item_span, "Missing `#[frame::runtime]`"))?,
			pallets: pallets
				.ok_or_else(|| syn::Error::new(item_span, "Missing `#[frame::pallets]`"))?,
        };

        Ok(def)
    }
}

mod keyword {
    syn::custom_keyword!(frame);
    syn::custom_keyword!(runtime);
	syn::custom_keyword!(pallets);
}

enum RuntimeAttr {
    Runtime(proc_macro2::Span),
	Pallets(proc_macro2::Span),
}

impl RuntimeAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Runtime(span) => *span,
			Self::Pallets(span) => *span,
		}
	}
}

impl syn::parse::Parse for RuntimeAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
        input.parse::<syn::Token![#]>()?;
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::frame>()?;
		content.parse::<syn::Token![::]>()?;

        let lookahead = content.lookahead1();
		if lookahead.peek(keyword::runtime) {
			Ok(RuntimeAttr::Runtime(content.parse::<keyword::runtime>()?.span()))
        }else if lookahead.peek(keyword::pallets) {
			Ok(RuntimeAttr::Pallets(content.parse::<keyword::pallets>()?.span()))
		} else {
			Err(lookahead.error())
		}
    }
}

fn construct_runtime_implicit_to_explicit(
	input: TokenStream2,
	definition: ImplicitAllPalletsDeclaration,
) -> Result<TokenStream2> {
	println!("construct_runtime_implicit_to_explicit");
	let frame_support = generate_crate_access_2018("frame-support")?;
	let mut expansion = quote::quote!(
		#[frame_support::construct_runtime_v2]
		#input
	);
	for pallet in definition.pallets.iter().filter(|pallet| pallet.pallet_parts.is_none()) {
		let pallet_path = &pallet.path;
		let pallet_name = &pallet.name;
		let pallet_instance = pallet.instance.as_ref().map(|instance| quote::quote!(::<#instance>));
		expansion = quote::quote!(
			#frame_support::tt_call! {
				macro = [{ #pallet_path::tt_default_parts_v2 }]
				frame_support = [{ #frame_support }]
				~~> #frame_support::match_and_insert! {
					target = [{ #expansion }]
					pattern = [{ #pallet_name: #pallet_path #pallet_instance }]
				}
			}
		);
	}

	Ok(expansion)
}

fn construct_runtime_explicit_to_explicit_expanded(
	input: TokenStream2,
	definition: ExplicitAllPalletsDeclaration,
) -> Result<TokenStream2> {
	println!("construct_runtime_explicit_to_explicit_expanded");
	let frame_support = generate_crate_access_2018("frame-support")?;
	let mut expansion = quote::quote!(
		#[frame_support::construct_runtime_v2]
		#input
	);
	for pallet in definition.pallets.iter().filter(|pallet| !pallet.is_expanded) {
		let pallet_path = &pallet.path;
		let pallet_name = &pallet.name;
		let pallet_instance = pallet.instance.as_ref().map(|instance| quote::quote!(::<#instance>));
		expansion = quote::quote!(
			#frame_support::tt_call! {
				macro = [{ #pallet_path::tt_extra_parts_v2 }]
				frame_support = [{ #frame_support }]
				~~> #frame_support::match_and_insert! {
					target = [{ #expansion }]
					pattern = [{ #pallet_name: #pallet_path #pallet_instance }]
				}
			}
		);
	}

	Ok(expansion)
}