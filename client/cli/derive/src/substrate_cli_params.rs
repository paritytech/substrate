// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Configuration trait for a CLI based on substrate

use proc_macro_error::{abort, abort_call_site};
use quote::{quote, ToTokens};
use std::collections::{HashMap, HashSet};
use syn::parse::Parser;
use syn::{punctuated::Punctuated, spanned::Spanned, *};

pub(crate) fn substrate_cli_params(
	a: proc_macro::TokenStream,
	i: proc_macro::TokenStream,
) -> proc_macro2::TokenStream {
	let attrs = match Punctuated::<ExprAssign, Token![,]>::parse_terminated.parse(a) {
		Ok(x) => x,
		Err(err) => abort!(err.span(), "could not parse attributes: {}", err),
	};

	let mut attrs = attrs
		.iter()
		.map(|x| {
			(
				match &*x.left {
					Expr::Path(p) if p.path.segments.len() == 1 => {
						p.path.segments[0].ident.to_string()
					}
					_ => abort!(x.left.span(), "could not parse token"),
				},
				(*x.right).to_token_stream(),
			)
		})
		.collect::<HashMap<_, _>>();

	let shared_params = attrs.remove("shared_params");
	let import_params = attrs.remove("import_params");
	let pruning_params = attrs.remove("pruning_params");
	let keystore_params = attrs.remove("keystore_params");
	let network_params = attrs.remove("network_params");
	let node_key_params = attrs.remove("node_key_params");

	if !attrs.is_empty() {
		abort_call_site!(
			"unknown macro parameters: {}",
			attrs
				.keys()
				.map(|x| x.as_str())
				.collect::<Vec<_>>()
				.join(", ")
		);
	}

	let mut i: ItemImpl = match syn::parse(i) {
		Ok(x) => x,
		_ => abort_call_site!("this macro only works on an impl"),
	};

	let existing_methods = i
		.items
		.iter()
		.filter_map(|x| match x {
			ImplItem::Method(x) => Some(x.sig.ident.to_string()),
			_ => None,
		})
		.collect::<HashSet<_>>();

	if let Some(path) = shared_params {
		if !existing_methods.contains("shared_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn shared_params(&self) -> &::sc_cli::SharedParams {
					&self.#path
				}
			}));
		}
	}

	if let Some(path) = import_params {
		if !existing_methods.contains("import_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn import_params(&self) -> ::std::option::Option<&::sc_cli::ImportParams> {
					Some(&self.#path)
				}
			}));
		}
	}

	if let Some(path) = pruning_params {
		if !existing_methods.contains("pruning_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn pruning_params(&self) -> ::std::option::Option<&::sc_cli::PruningParams> {
					Some(&self.#path)
				}
			}));
		}
	}

	if let Some(path) = keystore_params {
		if !existing_methods.contains("keystore_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn keystore_params(&self) -> ::std::option::Option<&::sc_cli::KeystoreParams> {
					Some(&self.#path)
				}
			}));
		}
	}

	if let Some(path) = node_key_params {
		if !existing_methods.contains("node_key_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn node_key_params(&self) -> ::std::option::Option<&::sc_cli::NodeKeyParams> {
					Some(&self.#path)
				}
			}));
		}
	}

	if let Some(path) = network_params {
		if !existing_methods.contains("network_params") {
			i.items.push(ImplItem::Verbatim(quote! {
				fn network_configuration_params(&self) -> ::std::option::Option<&::sc_cli::NetworkConfigurationParams> {
					Some(&self.#path)
				}
			}));
		}
	}

	quote!(#i)
}
