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

use frame_support_procedural_tools::syn_ext as ext;
use syn::{Ident, Result, Token, token};
use syn::parse::{Parse, ParseStream};
use crate::construct_runtime::parse::{convert_pallets, PalletsConversion, PalletDeclaration, Pallet};

#[derive(Debug, Clone)]
pub enum AllPalletsDeclaration {
	Implicit(ImplicitAllPalletsDeclaration),
	Explicit(ExplicitAllPalletsDeclaration),
	ExplicitExpanded(ExplicitAllPalletsDeclaration),
}

/// Declaration of a runtime with some pallet with implicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ImplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallets: Vec<PalletDeclaration>,
}

/// Declaration of a runtime with all pallet having explicit declaration of parts.
#[derive(Debug, Clone)]
pub struct ExplicitAllPalletsDeclaration {
	pub name: Ident,
	pub pallets: Vec<Pallet>,
	pub pallets_token: token::Brace,
}

impl Parse for AllPalletsDeclaration {
    fn parse(input: ParseStream) -> Result<Self> {
		input.parse::<Token![pub]>()?;

	   	// Support either `enum` or `struct`.
		if input.peek(Token![struct]) {
			input.parse::<Token![struct]>()?;
		} else {
			input.parse::<Token![enum]>()?;
		}

        let name = input.parse::<syn::Ident>()?;
        let pallets =
			input.parse::<ext::Braces<ext::Punctuated<PalletDeclaration, Token![,]>>>()?;
		let pallets_token = pallets.token;

        match convert_pallets(pallets.content.inner.into_iter().collect())? {
			PalletsConversion::Implicit(pallets) =>
				Ok(AllPalletsDeclaration::Implicit(ImplicitAllPalletsDeclaration {
					name,
					pallets,
				})),
			PalletsConversion::Explicit(pallets) =>
				Ok(AllPalletsDeclaration::Explicit(ExplicitAllPalletsDeclaration {
					name,
					pallets,
					pallets_token,
				})),
			PalletsConversion::ExplicitExpanded(pallets) =>
				Ok(AllPalletsDeclaration::ExplicitExpanded(ExplicitAllPalletsDeclaration {
					name,
					pallets,
					pallets_token,
				})),
		}
    }
}
