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
pub mod helper;

use syn::spanned::Spanned;
pub struct Def {
    pub item: syn::ItemMod,
    pub runtime_struct: runtime_struct::RuntimeStructDef,
}

impl Def {
	pub fn try_from(mut item: syn::ItemMod) -> syn::Result<Self> {
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

        for (index, item) in items.iter_mut().enumerate() {
            let runtime_attr: Option<RuntimeAttr> = helper::take_first_item_runtime_attr(item)?;

            match runtime_attr {
				Some(RuntimeAttr::Runtime(span)) if runtime_struct.is_none() => {
					let p = runtime_struct::RuntimeStructDef::try_from(span, index, item)?;
					runtime_struct = Some(p);
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
        };

        Ok(def)
    }
}

mod keyword {
    syn::custom_keyword!(frame);
    syn::custom_keyword!(runtime);
}

enum RuntimeAttr {
    Runtime(proc_macro2::Span),
}

impl RuntimeAttr {
	fn span(&self) -> proc_macro2::Span {
		match self {
			Self::Runtime(span) => *span,
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
        } else {
			Err(lookahead.error())
		}
    }
}
