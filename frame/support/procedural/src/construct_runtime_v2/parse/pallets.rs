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

use syn::{spanned::Spanned, Attribute, Ident};

pub struct PalletDef {
	/// The name of the pallet, e.g.`System` in `System: frame_system`.
	pub name: Ident,
	/// Optional attributes tagged right above a pallet declaration.
	pub attrs: Vec<Attribute>,
	/// Optional fixed index, e.g. `MyPallet ...  = 3,`.
	pub index: Option<u8>,
	/// The path of the pallet, e.g. `frame_system` in `System: frame_system`.
	pub path: syn::Path,
	/// The instance of the pallet, e.g. `Instance1` in `Council: pallet_collective::<Instance1>`.
	pub instance: Option<Ident>,
}

pub struct PalletsDef {
	pub ident: syn::Ident,
	pub pallets: Vec<PalletDef>,
}

impl PalletsDef {
	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Enum(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid frame::pallets, expect item enum."))
		};

		let mut pallets: Vec<PalletDef> = vec![]; 
		for variant in &item.variants {
			let (index, path) = match &variant.discriminant {
				Some((_, expr)) => {
					match expr {
						syn::Expr::Tuple(expr) => {
							if expr.elems.len() != 2 {
								return Err(
									syn::Error::new(item.span(), "Invalid pallet variant, expect tuple of size 2."));
							}
							match expr.elems[0] {
								syn::Expr::Lit(ref lit) => {
									match lit.lit {
										syn::Lit::Int(ref int) => {
											let index = int.base10_parse::<u8>().unwrap();
											match expr.elems[1] {
												syn::Expr::Path(ref path) => (Some(index), path.path.clone()),
												_ => return Err(
													syn::Error::new(item.span(), "Invalid pallet variant, expect tuple of size 2."))
											}
										},
										_ => return Err(
											syn::Error::new(item.span(), "Invalid pallet variant, expect tuple of size 2."))
									}
								},
								_ => return Err(
									syn::Error::new(item.span(), "Invalid pallet variant, expect tuple of size 2."))
							}
						},
						syn::Expr::Path(ref path) => (None, path.path.clone()),
						_ => unreachable!()
					}
				},
				None => unreachable!()
			};

			pallets.push(PalletDef {
				name: variant.ident.clone(),
				attrs: vec![],
				index,
				path,
				instance: None
			});
		};

		Ok(Self {
			ident: item.ident.clone(),
			pallets: pallets
		})
	}
}