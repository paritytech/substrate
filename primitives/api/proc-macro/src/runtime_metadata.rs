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

use proc_macro2::TokenStream;
use quote::quote;
use syn::{parse_quote, ImplItemMethod, ItemImpl, ItemTrait, Path, Result};

use crate::{
	common::CHANGED_IN_ATTRIBUTE,
	utils::{
		extract_impl_trait, filter_cfg_attributes, generate_decl_docs_getter,
		generate_runtime_mod_name_for_trait, get_doc_literals, RequireQualifiedTraitPath,
	},
};

fn add_where_type_bounds(ty: &syn::Type) -> Option<syn::Type> {
	let ty_string = format!("{}", quote!(#ty));
	// TODO: Rudimentary check.
	if !ty_string.contains("Block") {
		return None
	}

	// Remove the lifetime and mutability of the type T to
	// place bounds around it.
	let ty_elem = match &ty {
		syn::Type::Reference(reference) => &reference.elem,
		syn::Type::Ptr(ptr) => &ptr.elem,
		syn::Type::Slice(slice) => &slice.elem,
		syn::Type::Array(arr) => &arr.elem,
		_ => ty,
	};

	return Some(ty_elem.clone())
}

/// Generate decl metadata getters for `decl_runtime_api` macro.
///
/// The documentation is exposed for the runtime API metadata.
///
/// This method exposes the following functions for the latest trait version:
/// - `trait_[TRAIT_NAME]_decl_runtime_docs`: Extract trait documentation
/// - `[METHOD_NAME]_decl_runtime_docs`: One function for each method to extract its documentation
pub fn generate_decl_metadata(decl: &ItemTrait, crate_: &TokenStream) -> TokenStream {
	let mut methods = Vec::new();

	// Ensure that any function parameter that relies on the `BlockT` bounds
	// also has `TypeInfo + 'static` bounds (required by `scale_info::meta_type`).
	//
	// For example, if a runtime API defines a method that has an input:
	// `fn func(input: <Block as BlockT>::Header)`
	// then the runtime metadata will imply `<Block as BlockT>::Header: TypeInfo + 'static`.
	//
	// This restricts the bounds at the metadata level, without needing to modify the `BlockT`
	// itself, since the concrete implementations are already satisfying `TypeInfo`.
	let mut where_clause = Vec::new();
	for item in &decl.items {
		// Collect metadata for methods only.
		let syn::TraitItem::Method(method) = item else {
	                   continue
	    };

		let is_changed_in = method
			.attrs
			.iter()
			.find(|attr| attr.path.is_ident(CHANGED_IN_ATTRIBUTE))
			.is_some();
		if is_changed_in {
			continue
		}

		let mut inputs = Vec::new();

		let signature = &method.sig;

		for input in &signature.inputs {
			let syn::FnArg::Typed(typed) = input else {
					// Exclude `self` from metadata collection.
						   continue
				   };

			let pat = &typed.pat;
			let name = format!("{}", quote!(#pat));

			let ty = &typed.ty;

			add_where_type_bounds(ty).map(|ty_elem| where_clause.push(ty_elem));

			// if let Some(ty_elem) = add_where_type_bounds(ty) {
			// 	where_clause.push(quote!(#ty_elem: #crate_::scale_info::TypeInfo + 'static));
			// }

			// let ty_string = format!("{}", quote!(#ty));
			// // TODO: Rudimentary check.
			// if ty_string.contains("Block") {
			// 	// Remove the lifetime and mutability of the type T to
			// 	// place bounds around it.
			// 	// `**` dereference the &Box<T>, and `&` to not move T.
			// 	let ty_elem = match &**ty {
			// 		syn::Type::Reference(reference) => &reference.elem,
			// 		syn::Type::Ptr(ptr) => &ptr.elem,
			// 		syn::Type::Slice(slice) => &slice.elem,
			// 		syn::Type::Array(arr) => &arr.elem,
			// 		_ => ty,
			// 	};

			// 	// where_clause.push(quote!(#ty_elem: #crate_::scale_info::TypeInfo + 'static));
			// }

			inputs.push(quote!(
				#crate_::metadata::v15::ParamMetadata {
						name: #name,
						ty: #crate_::scale_info::meta_type::<#ty>(),
				}
			));
		}

		let output = match &signature.output {
			syn::ReturnType::Default => quote!(#crate_::scale_info::meta_type::<()>()),
			syn::ReturnType::Type(_, ty) => {
				add_where_type_bounds(ty).map(|ty_elem| where_clause.push(ty_elem));
				quote!(#crate_::scale_info::meta_type::<#ty>())
			},
		};

		// String method name including quotes for constructing `v15::MethodMetadata`.
		let method_name = format!("{}", signature.ident);
		let docs = if cfg!(feature = "no-metadata-docs") {
			quote!(#crate_::vec![])
		} else {
			// Function getter for the documentation.
			let docs = get_doc_literals(&method.attrs);
			quote!(#crate_::vec![ #( #docs, )* ])
		};

		let attrs = filter_cfg_attributes(&method.attrs);

		methods.push(quote!(
			#( #attrs )*
			#crate_::metadata::v15::MethodMetadata {
					name: #method_name,
					inputs: #crate_::vec![ #( #inputs, )* ],
					output: #output,
					docs: #docs,
			}
		));
	}

	let trait_name_ident = &decl.ident;
	let trait_name = format!("{}", trait_name_ident);

	let docs = if cfg!(feature = "no-metadata-docs") {
		quote!(#crate_::vec![])
	} else {
		let docs = get_doc_literals(&decl.attrs);
		quote!(#crate_::vec![ #( #docs, )* ])
	};

	let attrs = filter_cfg_attributes(&decl.attrs);
	// The trait generics where already extended with `Block: BlockT`.
	let mut generics = decl.generics.clone();
	for generic_param in generics.params.iter_mut() {
		let syn::GenericParam::Type(ty) = generic_param else {
			continue
		};

		// `scale_info::meta_type` needs `T: ?Sized + TypeInfo + 'static` bounds.
		ty.bounds.push(parse_quote!(#crate_::scale_info::TypeInfo));
		ty.bounds.push(parse_quote!('static));
	}

	let where_clause: Vec<_> = where_clause
		.iter()
		.map(|ty| quote!(#ty: #crate_::scale_info::TypeInfo + 'static))
		.collect();

	let res = quote!(
		#( #attrs )*
		#[inline(always)]
		pub fn runtime_metadata #generics () -> #crate_::metadata::v15::TraitMetadata
		where #( #where_clause, )*
		{
			#crate_::metadata::v15::TraitMetadata {
				name: #trait_name,
				methods: #crate_::vec![ #( #methods, )* ],
				docs: #docs,
			}
		}
	);

	// println!("res {}\n\n", res);

	res
}

/// Generate documentation getters for `decl_runtime_api` macro.
///
/// The documentation is exposed for the runtime API metadata.
///
/// This method exposes the following functions for the latest trait version:
/// - `trait_[TRAIT_NAME]_decl_runtime_docs`: Extract trait documentation
/// - `[METHOD_NAME]_decl_runtime_docs`: One function for each method to extract its documentation
pub fn generate_decl_docs(decl: &ItemTrait, crate_: &TokenStream) -> TokenStream {
	if cfg!(feature = "no-metadata-docs") {
		return quote!()
	}

	let mut methods = Vec::new();

	for item in &decl.items {
		// Collect metadata for methods only.
		let syn::TraitItem::Method(method) = item else {
	                   continue
	    };

		let signature = &method.sig;
		let method_name = generate_decl_docs_getter(&signature.ident, false);

		let is_changed_in = method
			.attrs
			.iter()
			.find(|attr| attr.path.is_ident(CHANGED_IN_ATTRIBUTE))
			.is_some();
		// Report docs for the latest methods only.
		if is_changed_in {
			continue
		}

		let attrs = filter_cfg_attributes(&method.attrs);
		let docs = get_doc_literals(&method.attrs);
		methods.push(quote!(
				#( #attrs )*
				pub fn #method_name() -> #crate_::vec::Vec<&'static str> {
						#crate_::vec![ #( #docs, )* ]
				}
		));
	}

	let trait_name = generate_decl_docs_getter(&decl.ident, true);
	let docs = get_doc_literals(&decl.attrs);
	let attrs = filter_cfg_attributes(&decl.attrs);

	quote!(
			#( #attrs )*
			pub fn #trait_name() -> #crate_::vec::Vec<&'static str> {
					#crate_::vec![ #( #docs, )* ]
			}

			#( #methods )*
	)
}

/// Generate the runtime metadata for a given method.
fn generate_method_metadata(
	method: &ImplItemMethod,
	crate_: &TokenStream,
	hidden_mod: &Path,
) -> Result<TokenStream> {
	let signature = &method.sig;
	let mut inputs = Vec::new();

	for input in &signature.inputs {
		let syn::FnArg::Typed(typed) = input else {
				// Exclude `self` from metadata collection.
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

	// String method name including quotes for constructing `v15::MethodMetadata`.
	let method_name = format!("{}", signature.ident);
	let docs = if cfg!(feature = "no-metadata-docs") {
		quote!(crate_::vec![])
	} else {
		// Function getter for the documentation.
		let doc_getter = generate_decl_docs_getter(&signature.ident, false);
		quote!(#hidden_mod::#doc_getter())
	};

	let attrs = filter_cfg_attributes(&method.attrs);

	Ok(quote!(
			#( #attrs )*
			#crate_::metadata::v15::MethodMetadata {
					name: #method_name,
					inputs: #crate_::vec![ #( #inputs, )* ],
					output: #output,
					docs: #docs,
			}
	))
}

/// Generate the runtime metadata for a given trait.
fn generate_trait_metadata(impl_: &ItemImpl, crate_: &TokenStream) -> Result<TokenStream> {
	let mut trait_ = extract_impl_trait(&impl_, RequireQualifiedTraitPath::Yes)?.clone();

	// Implementation traits are always references with a path `impl client::Core ...`
	// The trait name is the last segment of this path.
	let trait_name_ident = &trait_
		.segments
		.last()
		.as_ref()
		.expect("Trait path should always contain at least one item; qed")
		.ident;

	let trait_doc_getter = generate_decl_docs_getter(trait_name_ident, true);
	let trait_name = format!("{}", trait_name_ident);

	// Generate `runtime_decl_for_[TRAIT_NAME]` module that contains the documentation getters.
	let runtime_decl_mod = generate_runtime_mod_name_for_trait(trait_name_ident);

	// Get absolute path to the `runtime_decl_for_` module by replacing the last segment.
	if let Some(segment) = trait_.segments.last_mut() {
		*segment = parse_quote!(#runtime_decl_mod);
	}

	let docs = if cfg!(feature = "no-metadata-docs") {
		quote!(crate_::vec![])
	} else {
		quote!(#trait_::#trait_doc_getter())
	};

	let attrs = filter_cfg_attributes(&impl_.attrs);

	let mut methods = Vec::new();
	for item in &impl_.items {
		// Collect metadata for methods only.
		let syn::ImplItem::Method(method) = item else {
                       continue;
        };

		let metadata = generate_method_metadata(&method, crate_, &trait_)?;
		methods.push(metadata);
	}

	Ok(quote!(
			#( #attrs )*
			#crate_::metadata::v15::TraitMetadata {
					name: #trait_name,
					methods: #crate_::vec![ #( #methods, )* ],
					docs: #docs,
			}
	))
}

/// Generate the runtime metadata for the given traits.
pub fn generate_runtime_metadata(impls: &[ItemImpl], crate_: &TokenStream) -> Result<TokenStream> {
	if impls.is_empty() {
		return Ok(quote!())
	}

	// Get the name of the runtime for which the traits are implemented.
	let runtime_name = &impls
		.get(0)
		.expect("Traits should contain at least one implementation; qed")
		.self_ty;

	let mut metadata = Vec::new();

	for impl_ in impls {
		metadata.push(generate_trait_metadata(impl_, &crate_)?);
	}

	Ok(quote!(
		impl #runtime_name {
			pub fn runtime_metadata() -> #crate_::vec::Vec<#crate_::metadata::v15::TraitMetadata> {
				#crate_::vec![ #( #metadata, )* ]
			}
		}
	))
}

/// Generate the runtime metadata for the given traits.
pub fn generate_runtime_metadata2(impls: &[ItemImpl], crate_: &TokenStream) -> Result<TokenStream> {
	if impls.is_empty() {
		return Ok(quote!())
	}

	// Get the name of the runtime for which the traits are implemented.
	let runtime_name = &impls
		.get(0)
		.expect("Traits should contain at least one implementation; qed")
		.self_ty;
	// TODO: only one runtime is supported.

	let mut metadata = Vec::new();

	for impl_ in impls {
		println!("impl_ {}", quote!(#impl_));
		let defaultness = &impl_.defaultness;
		println!("impl_defaultness {}", quote!(#defaultness));
		let unsafety = &impl_.unsafety;
		println!("unsafety {}", quote!(#unsafety));
		let generics = &impl_.generics;
		println!("generics {}", quote!(#generics));

		let trait_ = &impl_.trait_;
		trait_.as_ref().map(|(_, p, _)| println!("path {}", quote!(#p)));

		let self_ty = &impl_.self_ty;
		println!("self_ty {}", quote!(#self_ty));

		// let brace_token = &impl_.brace_token;
		// println!("brace_token {}", quote!(#brace_token));

		// let items = &impl_.items;
		// println!("items {}", quote!(#items));

		let mut trait_ = extract_impl_trait(&impl_, RequireQualifiedTraitPath::Yes)?.clone();

		// Implementation traits are always references with a path `impl client::Core ...`
		// The trait name is the last segment of this path.
		let trait_name_ident = &trait_
			.segments
			.last()
			.as_ref()
			.expect("Trait path should always contain at least one item; qed")
			.ident;

		let mod_name = generate_runtime_mod_name_for_trait(&trait_name_ident);

		let generics = trait_
			.segments
			.iter()
			.find_map(|segment| {
				if let syn::PathArguments::AngleBracketed(generics) = &segment.arguments {
					Some(generics.clone())
				} else {
					None
				}
			})
			.expect("Trait path should always contain at least one generic parameter; qed");

		let gen = generics.clone();
		println!("          Generics: {}", quote!(#gen));

		// for segment in &trait_.segments {
		// 	let syn::PathArguments::AngleBracketed(generics) = &segment.arguments else {
		// 		continue;
		// 	}

		// 	match &segment.arguments {
		// 		syn::PathArguments::None => todo!(),
		// 		syn::PathArguments::AngleBracketed(_) => todo!(),
		// 		syn::PathArguments::Parenthesized(_) => todo!(),
		// 	}

		// }

		// Get absolute path to the `runtime_decl_for_` module by replacing the last segment.
		if let Some(segment) = trait_.segments.last_mut() {
			*segment = parse_quote!(#mod_name);
		}

		let attrs = filter_cfg_attributes(&impl_.attrs);
		// let generics = &impl_.generics;
		// let trait_ = &impl_.trait_;
		let self_ty = &impl_.self_ty;

		println!("generics {}", quote!(#generics));
		println!("trait_ {}", quote!(#trait_));
		println!("self_ty {}\n", quote!(#self_ty));

		metadata.push(quote!(
			#( #attrs )*
			#trait_::runtime_metadata::#generics()
		));
	}

	Ok(quote!(
		impl #runtime_name {
			pub fn runtime_metadata() -> #crate_::vec::Vec<#crate_::metadata::v15::TraitMetadata> {
				#crate_::vec![ #( #metadata, )* ]
			}
		}
	))
}

// 		let mod_name = generate_runtime_mod_name_for_trait(&decl.ident);
