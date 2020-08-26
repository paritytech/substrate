// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

mod parse;

use frame_support_procedural_tools::syn_ext as ext;
use frame_support_procedural_tools::{generate_crate_access, generate_hidden_includes};
use parse::{ModuleDeclaration, RuntimeDefinition, WhereSection};
use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2, Span};
use quote::quote;
use syn::{Ident, Result, TypePath};

/// The fixed name of the system module.
const SYSTEM_MODULE_NAME: &str = "System";

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	construct_runtime_parsed(definition)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn construct_runtime_parsed(definition: RuntimeDefinition) -> Result<TokenStream2> {
	let RuntimeDefinition {
		name,
		deprecated_system_non_zero,
		where_section: WhereSection {
			block,
			node_block,
			unchecked_extrinsic,
			..
		},
		modules:
			ext::Braces {
				content: ext::Punctuated { inner: modules, .. },
				token: modules_token,
			},
		..
	} = definition;
	let modules = modules.into_iter().collect::<Vec<_>>();

	let system_module = check_modules(deprecated_system_non_zero, &modules, modules_token.span)?;

	let hidden_crate_name = "construct_runtime";
	let scrate = generate_crate_access(&hidden_crate_name, "frame-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "frame-support");

	let all_but_system_modules = modules.clone().into_iter()
		.filter(|module| module.name != SYSTEM_MODULE_NAME)
		.collect::<Vec<_>>();

	let outer_event = decl_outer_event(
		&name,
		&modules,
		&scrate,
	)?;

	let outer_origin = decl_outer_origin(
		&name,
		&all_but_system_modules,
		&system_module,
		&scrate,
	)?;
	let all_modules = decl_all_modules(&name, modules.iter());
	let module_to_index = decl_module_to_index(&modules, &scrate);

	let dispatch = decl_outer_dispatch(&name, &modules, &scrate);
	let metadata = decl_runtime_metadata(&name, modules.iter(), &scrate, &unchecked_extrinsic);
	let outer_config = decl_outer_config(&name, modules.iter(), &scrate);
	let inherent = decl_outer_inherent(
		&block,
		&unchecked_extrinsic,
		modules.iter(),
		&scrate,
	);
	let validate_unsigned = decl_validate_unsigned(&name, modules.iter(), &scrate);
	let integrity_test = decl_integrity_test(&scrate);

	let res = quote!(
		#scrate_decl

		#[derive(Clone, Copy, PartialEq, Eq, #scrate::sp_runtime::RuntimeDebug)]
		pub struct #name;
		impl #scrate::sp_runtime::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl #scrate::sp_runtime::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}

		#outer_event

		#outer_origin

		#all_modules

		#module_to_index

		#dispatch

		#metadata

		#outer_config

		#inherent

		#validate_unsigned

		#integrity_test
	);

	Ok(res.into())
}

fn decl_validate_unsigned<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter(|module_declaration| module_declaration.exists_part("ValidateUnsigned"))
		.map(|module_declaration| &module_declaration.name);
	quote!(
		#scrate::impl_outer_validate_unsigned!(
			impl ValidateUnsigned for #runtime {
				#( #modules_tokens )*
			}
		);
	)
}

fn decl_outer_inherent<'a>(
	block: &'a syn::TypePath,
	unchecked_extrinsic: &'a syn::TypePath,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations.filter_map(|module_declaration| {
		let maybe_config_part = module_declaration.find_part("Inherent");
		maybe_config_part.map(|_| {
			let name = &module_declaration.name;
			quote!(#name,)
		})
	});
	quote!(
		#scrate::impl_outer_inherent!(
			impl Inherents where
				Block = #block,
				UncheckedExtrinsic = #unchecked_extrinsic
			{
				#(#modules_tokens)*
			}
		);
	)
}

fn decl_outer_config<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter_map(|module_declaration| {
			module_declaration.find_part("Config").map(|part| {
				let transformed_generics: Vec<_> = part
					.generics
					.params
					.iter()
					.map(|param| quote!(<#param>))
					.collect();
				(module_declaration, transformed_generics)
			})
		})
		.map(|(module_declaration, generics)| {
			let module = &module_declaration.module;
			let name = Ident::new(
				&format!("{}Config", module_declaration.name),
				module_declaration.name.span(),
			);
			let instance = module_declaration.instance.as_ref().into_iter();
			quote!(
				#name =>
					#module #(#instance)* #(#generics)*,
			)
		});
	quote!(
		#scrate::sp_runtime::impl_outer_config! {
			pub struct GenesisConfig for #runtime {
				#(#modules_tokens)*
			}
		}
	)
}

fn decl_runtime_metadata<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
	extrinsic: &TypePath,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter_map(|module_declaration| {
			module_declaration.find_part("Module").map(|_| {
				let filtered_names: Vec<_> = module_declaration
					.module_parts()
					.into_iter()
					.filter(|part| part.name() != "Module")
					.map(|part| part.ident())
					.collect();
				(module_declaration, filtered_names)
			})
		})
		.map(|(module_declaration, filtered_names)| {
			let module = &module_declaration.module;
			let name = &module_declaration.name;
			let instance = module_declaration
				.instance
				.as_ref()
				.map(|name| quote!(<#name>))
				.into_iter();

			let index = module_declaration.index.map(|index| quote::quote!( { index #index } ));

			quote!(
				#module::Module #(#instance)* as #name with #(#filtered_names)* #index,
			)
		});
	quote!(
		#scrate::impl_runtime_metadata!{
			for #runtime with modules where Extrinsic = #extrinsic
				#(#modules_tokens)*
		}
	)
}

fn decl_outer_dispatch<'a>(
	runtime: &'a Ident,
	module_declarations: &Vec<ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let mut available_indices = get_available_indices(module_declarations);
	let modules_tokens = module_declarations.iter()
		.filter(|module_declaration| module_declaration.exists_part("Call"))
		.map(|module_declaration| {
			let module = &module_declaration.module;
			let name = &module_declaration.name;
			let index = match module_declaration.index {
				Some(index) => index,
				None => available_indices.remove(0),
			};
			let index_string = syn::LitStr::new(&format!("{}", index), Span::call_site());
			quote!(#[codec(index = #index_string)] #module::#name)
		});

	quote!(
		#scrate::impl_outer_dispatch! {
			pub enum Call for #runtime where origin: Origin {
				#(#modules_tokens,)*
			}
		}
	)
}

fn decl_outer_origin<'a>(
	runtime_name: &'a Ident,
	modules_except_system: &Vec<ModuleDeclaration>,
	system_name: &'a Ident,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
	let mut available_indices = get_available_indices(modules_except_system);
	available_indices.retain(|i| *i != 0); // index 0 is reserved for system in origin
	for module_declaration in modules_except_system {
		match module_declaration.find_part("Origin") {
			Some(module_entry) => {
				let module = &module_declaration.module;
				let instance = module_declaration.instance.as_ref();
				let generics = &module_entry.generics;
				if instance.is_some() && generics.params.len() == 0 {
					let msg = format!(
						"Instantiable module with no generic `Origin` cannot \
						 be constructed: module `{}` must have generic `Origin`",
						module_declaration.name
					);
					return Err(syn::Error::new(module_declaration.name.span(), msg));
				}
				let index = match module_declaration.index {
					Some(index) => {
						assert!(index != 0, "Internal error, some origin is at index 0");
						index
					},
					None => available_indices.remove(0),
				};
				let index_string = syn::LitStr::new(&format!("{}", index), Span::call_site());
				let tokens = quote!(#[codec(index = #index_string)] #module #instance #generics ,);
				modules_tokens.extend(tokens);
			}
			None => {}
		}
	}

	Ok(quote!(
		#scrate::impl_outer_origin! {
			pub enum Origin for #runtime_name where system = #system_name {
				#modules_tokens
			}
		}
	))
}

fn decl_outer_event<'a>(
	runtime_name: &'a Ident,
	module_declarations: &Vec<ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
	let mut available_indices = get_available_indices(module_declarations);
	for module_declaration in module_declarations {
		match module_declaration.find_part("Event") {
			Some(module_entry) => {
				let module = &module_declaration.module;
				let instance = module_declaration.instance.as_ref();
				let generics = &module_entry.generics;
				if instance.is_some() && generics.params.len() == 0 {
					let msg = format!(
						"Instantiable module with no generic `Event` cannot \
						 be constructed: module `{}` must have generic `Event`",
						module_declaration.name,
					);
					return Err(syn::Error::new(module_declaration.name.span(), msg));
				}

				let index = match module_declaration.index {
					Some(index) => index,
					None => available_indices.remove(0),
				};
				let index_string = syn::LitStr::new(&format!("{}", index), Span::call_site());
				let tokens = quote!(#[codec(index = #index_string)] #module #instance #generics,);
				modules_tokens.extend(tokens);
			}
			None => {}
		}
	}

	Ok(quote!(
		#scrate::impl_outer_event! {
			pub enum Event for #runtime_name {
				#modules_tokens
			}
		}
	))
}

fn decl_all_modules<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
) -> TokenStream2 {
	let mut types = TokenStream2::new();
	let mut names = Vec::new();
	for module_declaration in module_declarations {
		let type_name = &module_declaration.name;
		let module = &module_declaration.module;
		let mut generics = vec![quote!(#runtime)];
		generics.extend(
			module_declaration
				.instance
				.iter()
				.map(|name| quote!(#module::#name)),
		);
		let type_decl = quote!(
			pub type #type_name = #module::Module <#(#generics),*>;
		);
		types.extend(type_decl);
		names.push(&module_declaration.name);
	}
	// Make nested tuple structure like (((Babe, Consensus), Grandpa), ...)
	// But ignore the system module.
	let all_modules = names.iter()
		.filter(|n| **n != SYSTEM_MODULE_NAME)
		.fold(TokenStream2::default(), |combined, name| quote!((#name, #combined)));

	quote!(
		#types
		type AllModules = ( #all_modules );
	)
}

fn decl_module_to_index<'a>(
	module_declarations: &Vec<ModuleDeclaration>,
	scrate: &TokenStream2,
) -> TokenStream2 {
	let names = module_declarations.iter().map(|d| &d.name);
	let mut available_indices = get_available_indices(module_declarations);
	let indices = module_declarations.iter()
		.map(|module| {
			match module.index {
				Some(index) => index as usize,
				None => available_indices.remove(0) as usize,
			}
		});

	quote!(
		/// Provides an implementation of `ModuleToIndex` to map a module
		/// to its index in the runtime.
		pub struct ModuleToIndex;

		impl #scrate::traits::ModuleToIndex for ModuleToIndex {
			fn module_to_index<M: 'static>() -> Option<usize> {
				let type_id = #scrate::sp_std::any::TypeId::of::<M>();
				#(
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#indices)
					}
				)*

				None
			}
		}
	)
}

fn decl_integrity_test(scrate: &TokenStream2) -> TokenStream2 {
	quote!(
		#[cfg(test)]
		mod __construct_runtime_integrity_test {
			use super::*;

			#[test]
			pub fn runtime_integrity_tests() {
				<AllModules as #scrate::traits::IntegrityTest>::integrity_test();
			}
		}
	)
}

fn get_available_indices(modules: &Vec<ModuleDeclaration>) -> Vec<u8> {
	let reserved_indices = modules.iter()
		.filter_map(|module| module.index)
		.collect::<Vec<_>>();

	(0..u8::max_value())
	.filter(|i| !reserved_indices.contains(i))
	.collect::<Vec<_>>()
}

/// Check:
/// * check system module is defined
/// * there is less than 256 modules
/// * no module use index 0 or except system
/// * system module index is 0 (either explicitly or implicitly).
/// * module indices don't conflict.
///
/// returns system module ident
fn check_modules(
	deprecated_system_non_zero: bool,
	modules: &Vec<ModuleDeclaration>,
	modules_span: proc_macro2::Span,
) -> Result<syn::Ident> {
	// Assert we have system module declared
	let system_module = modules.iter()
		.find(|decl| decl.name == SYSTEM_MODULE_NAME)
		.ok_or_else(|| syn::Error::new(
			modules_span,
			"`System` module declaration is missing. \
			 Please add this line: `System: frame_system::{Module, Call, Storage, Config, Event<T>},`",
		))?;

	if modules.len() > u8::max_value() as usize {
		let msg = "Too many modules defined, only 256 modules is currently allowed";
		return Err(syn::Error::new(modules_span, msg));
	}

	// No module use index 0
	if let Some(module) = modules.iter()
		.find(|module| {
			module.index.map_or(false, |i| i == 0) && module.name != SYSTEM_MODULE_NAME
		})
	{
		let msg = format!(
			"Only system module is allowed to be defined at index `0`",
		);
		return Err(syn::Error::new(module.name.span(), msg));
	}

	if !deprecated_system_non_zero {
		if let Some(index) = system_module.index {
			// System module is at index 0 explicitly
			if index != 0 {
				let msg = "System module must be defined at index `0`";
				return Err(syn::Error::new(system_module.module.span(), msg));
			}
		} else {
			// System module is at index 0 implicitly
			let first_implicit_module = modules.iter().filter(|m| m.index.is_none()).next()
				.expect("At least system module exists; qed");

			if first_implicit_module.name != SYSTEM_MODULE_NAME {
				let msg = format!(
					"System module must be defined at index `0`, instead {} is found. (this check \
					is to avoid confusion for generation of origin_caller, (where system is \
					forced to be at index 0 anyway), to bypass this check use attribute \
					`#[deprecated_system_non_zero]` as \
					`construct_runtime!(#[deprecated_system_non_zero] ... )`).",
					first_implicit_module.name,
				);
				return Err(syn::Error::new(first_implicit_module.module.span(), msg));
			}
		}
	}

	// No module indices conflicts
	let mut indices = vec![];
	for module in modules {
		if let Some(index) = module.index {
			if indices.contains(&index) {
				return Err(syn::Error::new(module.module.span(), "module index is already used"));
			} else {
				indices.push(index)
			}
		}
	}

	Ok(system_module.module.clone())
}
