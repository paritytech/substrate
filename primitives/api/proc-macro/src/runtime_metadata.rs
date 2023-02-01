// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

use proc_macro2::{Ident, TokenStream};
use quote::{format_ident, quote};
use syn::{
	parse::{Error, Result},
	parse_quote, ImplItemMethod, ItemImpl, ItemTrait, Path, TraitItemMethod,
};

use crate::{
	common::CHANGED_IN_ATTRIBUTE,
	utils::{extract_impl_trait, generate_runtime_mod_name_for_trait, RequireQualifiedTraitPath},
};

fn get_doc_literals(attrs: &[syn::Attribute]) -> Vec<syn::Lit> {
	attrs
		.iter()
		.filter_map(|attr| {
			let Ok(syn::Meta::NameValue(meta)) = attr.parse_meta() else {
				return None
			};

			if meta.path.get_ident().map_or(false, |ident| ident == "doc") {
				Some(meta.lit)
			} else {
				None
			}
		})
		.collect()
}

// // Filters all attributes except the cfg ones.
// fn filter_cfg_attrs(attrs: &[Attribute]) -> Vec<Attribute> {
// 	attrs.iter().filter(|a| a.path.is_ident("cfg")).cloned().collect()
// }

fn get_cfg_attributes(attrs: &[syn::Attribute]) -> Vec<syn::Attribute> {
	attrs.iter().filter(|a| a.path.is_ident("cfg")).cloned().collect()
}

fn generate_method_metadata(method: &TraitItemMethod, crate_: &TokenStream) -> Result<TokenStream> {
	let signature = &method.sig;
	let method_name = format!("{}", signature.ident);
	let attrs = get_cfg_attributes(&method.attrs);
	let docs = get_doc_literals(&method.attrs);

	let mut inputs = Vec::new();

	for input in &signature.inputs {
		let syn::FnArg::Typed(typed) = input else {
			continue
			// return Err(Error::new(
			// 	signature.ident.span(),
			// 	"The `self` parameter is unsuppoted for the runtime method. \
			// 	Please remove it or use a typed representation as `self: Box<Self>`"
			// ))
		};

		let pat = &typed.pat;
		let name = format!("{}", quote!(#pat));
		let ty = &typed.ty;

		inputs.push(quote!(
			#crate_::metadata::v15::ParamMetadata {
				name: #name,
				ty: #crate_::scale_info::meta_type::<#ty>(),
			}
		));
	}

	let output = match &signature.output {
		syn::ReturnType::Default => quote!(#crate_::scale_info::meta_type::<()>()),
		syn::ReturnType::Type(_, ty) => quote!(#crate_::scale_info::meta_type::<#ty>()),
	};

	Ok(quote!(
		#( #attrs )*
		#crate_::metadata::v15::MethodMetadata {
			name: #method_name,
			inputs: #crate_::vec![ #( #inputs, )* ],
			output: #output,
			docs: #crate_::vec![ #( #docs, )* ],
		}
	))
}

pub fn generate_trait_metadata_docs(decl: &ItemTrait, crate_: &TokenStream) -> TokenStream {
	let docs = get_doc_literals(&decl.attrs);
	let attrs = get_cfg_attributes(&decl.attrs);

	let mut methods = Vec::new();
	for item in &decl.items {
		// Collect metadata for methods only.
		let syn::TraitItem::Method(method) = item else {
			continue
        };

		let signature = &method.sig;
		let method_name = format_ident!("{}_runtime_docs", signature.ident);

		let is_changed_in = method
			.attrs
			.iter()
			.find(|attr| attr.path.is_ident(CHANGED_IN_ATTRIBUTE))
			.is_some();
		// Report docs for the latest methods only.
		if is_changed_in {
			continue
		}

		let attrs = get_cfg_attributes(&method.attrs);
		let docs = get_doc_literals(&method.attrs);
		methods.push(quote!(
			#( #attrs )*
			pub fn #method_name() -> #crate_::vec::Vec<&'static str> {
				#crate_::vec![ #( #docs, )* ]
			}
		));
	}

	// let no_docs = vec![];
	// let docs = if cfg!(feature = "no-metadata-docs") { &no_docs } else { &docs };

	quote!(
		#( #attrs )*
		pub fn trait_runtime_docs() -> #crate_::vec::Vec<&'static str> {
			#crate_::vec![ #( #docs, )* ]
		}

		#( #methods )*
	)
}

pub fn generate_trait_metadata(decl: &ItemTrait, crate_: &TokenStream) -> Result<TokenStream> {
	let trait_name = format!("{}", &decl.ident);
	let docs = get_doc_literals(&decl.attrs);
	let attrs = get_cfg_attributes(&decl.attrs);

	let mut methods = Vec::new();
	for item in &decl.items {
		// Collect metadata for methods only.
		let syn::TraitItem::Method(method) = item else {
				return Err(Error::new(
					decl.ident.span(),
					"Runtime traits are supporting only method declarations"
				));
        };

		let metadata = generate_method_metadata(method, crate_)?;
		methods.push(metadata);
	}

	let res = quote!(
		// !!INTERNAL USE ONLY!!
		// #[doc(hidden)]
		// pub fn __runtime_api_internal_metadata(&self) -> #crate_::metadata::v15::TraitMetadata {
		#( #attrs )*
		#crate_::metadata::v15::TraitMetadata {
			name: #trait_name,
			methods: #crate_::vec![ #( #methods, )* ],
			docs: #crate_::vec![ #( #docs, )* ],
		}
		// }
	);

	// println!("Res: {}", res);
	Ok(res)
}

fn generate_2method_metadata(
	method: &ImplItemMethod,
	crate_: &TokenStream,
	hidden_mod: &Path,
) -> Result<TokenStream> {
	let signature = &method.sig;
	// String collected by `MethodMetadata`.
	let method_name = format!("{}", signature.ident);
	// Function getter for the documentation.
	let doc_getter = format_ident!("{}_{}", signature.ident, "runtime_docs");

	let attrs = get_cfg_attributes(&method.attrs);
	let docs = get_doc_literals(&method.attrs);

	let mut inputs = Vec::new();

	for input in &signature.inputs {
		let syn::FnArg::Typed(typed) = input else {
			continue
		};

		let pat = &typed.pat;
		let name = format!("{}", quote!(#pat));
		let ty = &typed.ty;

		inputs.push(quote!(
			#crate_::metadata::v15::ParamMetadata {
				name: #name,
				ty: #crate_::scale_info::meta_type::<#ty>(),
			}
		));
	}

	let output = match &signature.output {
		syn::ReturnType::Default => quote!(#crate_::scale_info::meta_type::<()>()),
		syn::ReturnType::Type(_, ty) => quote!(#crate_::scale_info::meta_type::<#ty>()),
	};

	Ok(quote!(
		#( #attrs )*
		#crate_::metadata::v15::MethodMetadata {
			name: #method_name,
			inputs: #crate_::vec![ #( #inputs, )* ],
			output: #output,
			docs: #hidden_mod::#doc_getter(),
		}
	))
}

pub fn generate_2trait_metadata(impl_: &ItemImpl, crate_: &TokenStream) -> Result<TokenStream> {
	let mut trait_ = extract_impl_trait(&impl_, RequireQualifiedTraitPath::Yes)?.clone();

	// Implementation traits are always references with a path `impl client::Core ...`
	// The trait name is the last segment of this path.
	let trait_name_ident = &trait_
		.segments
		.last()
		.as_ref()
		.expect("Trait path should always contain at least one item; qed")
		.ident;

	let trait_name = format!("{}", trait_name_ident);

	// Generate `runtime_decl_for_[TRAIT_NAME]` module that contains the documentation getters.
	let runtime_decl_mod = generate_runtime_mod_name_for_trait(trait_name_ident);

	// Get absolute path to the `runtime_decl_for_` module by replacing the last segment.
	if let Some(segment) = trait_.segments.last_mut() {
		*segment = parse_quote!(#runtime_decl_mod);
	}

	let docs = get_doc_literals(&impl_.attrs);
	let attrs = get_cfg_attributes(&impl_.attrs);

	let mut methods = Vec::new();
	for item in &impl_.items {
		// Collect metadata for methods only.
		let syn::ImplItem::Method(method) = item else {
			continue;
        };

		let metadata = generate_2method_metadata(&method, crate_, &trait_)?;
		methods.push(metadata);
	}

	let res = quote!(
		// !!INTERNAL USE ONLY!!
		// #[doc(hidden)]
		// pub fn __runtime_api_internal_metadata(&self) -> #crate_::metadata::v15::TraitMetadata {
		#( #attrs )*
		#crate_::metadata::v15::TraitMetadata {
			name: #trait_name,
			methods: #crate_::vec![ #( #methods, )* ],
			docs: #trait_::trait_runtime_docs(),
		}
	);

	Ok(res)
}
