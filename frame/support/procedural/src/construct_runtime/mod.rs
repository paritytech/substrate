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
use parse::{ModuleDeclaration, RuntimeDefinition, WhereSection, ModulePart};
use proc_macro::TokenStream;
use proc_macro2::{TokenStream as TokenStream2};
use quote::quote;
use syn::{Ident, Result, TypePath};
use std::collections::HashMap;

/// The fixed name of the system module.
const SYSTEM_MODULE_NAME: &str = "System";

/// The complete definition of a module with the resulting fixed index.
#[derive(Debug, Clone)]
pub struct Module {
	pub name: Ident,
	pub index: u8,
	pub module: Ident,
	pub instance: Option<Ident>,
	pub module_parts: Vec<ModulePart>,
}

impl Module {
	/// Get resolved module parts
	fn module_parts(&self) -> &[ModulePart] {
		&self.module_parts
	}

	/// Find matching parts
	fn find_part(&self, name: &str) -> Option<&ModulePart> {
		self.module_parts.iter().find(|part| part.name() == name)
	}

	/// Return whether module contains part
	fn exists_part(&self, name: &str) -> bool {
		self.find_part(name).is_some()
	}
}

/// Convert from the parsed module to their final information.
/// Assign index to each modules using same rules as rust for fieldless enum.
/// I.e. implicit are assigned number incrementedly from last explicit or 0.
fn complete_modules(decl: impl Iterator<Item = ModuleDeclaration>) -> syn::Result<Vec<Module>> {
	let mut indices = HashMap::new();
	let mut last_index: Option<u8> = None;

	decl
		.map(|module| {
			let final_index = match module.index {
				Some(i) => i,
				None => last_index.map_or(Some(0), |i| i.checked_add(1))
					.ok_or_else(|| {
						let msg = "Module index doesn't fit into u8, index is 256";
						syn::Error::new(module.name.span(), msg)
					})?,
			};

			last_index = Some(final_index);

			if let Some(used_module) = indices.insert(final_index, module.name.clone()) {
				let msg = format!(
					"Module indices are conflicting: Both modules {} and {} are at index {}",
					used_module,
					module.name,
					final_index,
				);
				let mut err = syn::Error::new(used_module.span(), &msg);
				err.combine(syn::Error::new(module.name.span(), msg));
				return Err(err);
			}

			Ok(Module {
				name: module.name,
				index: final_index,
				module: module.module,
				instance: module.instance,
				module_parts: module.module_parts,
			})
		})
		.collect()
}

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	construct_runtime_parsed(definition)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn construct_runtime_parsed(definition: RuntimeDefinition) -> Result<TokenStream2> {
	let RuntimeDefinition {
		name,
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

	let modules = complete_modules(modules.into_iter())?;

	let system_module = modules.iter()
		.find(|decl| decl.name == SYSTEM_MODULE_NAME)
		.ok_or_else(|| syn::Error::new(
			modules_token.span,
			"`System` module declaration is missing. \
			 Please add this line: `System: frame_system::{Module, Call, Storage, Config, Event<T>},`",
		))?;

	let hidden_crate_name = "construct_runtime";
	let scrate = generate_crate_access(&hidden_crate_name, "frame-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "frame-support");

	let all_but_system_modules = modules.iter().filter(|module| module.name != SYSTEM_MODULE_NAME);

	let outer_event = decl_outer_event(
		&name,
		modules.iter(),
		&scrate,
	)?;

	let outer_origin = decl_outer_origin(
		&name,
		all_but_system_modules,
		&system_module,
		&scrate,
	)?;
	let all_modules = decl_all_modules(&name, modules.iter());
	let module_to_index = decl_pallet_runtime_setup(&modules, &scrate);

	let dispatch = decl_outer_dispatch(&name, modules.iter(), &scrate);
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

		// Prevent UncheckedExtrinsic to print unused warning.
		const _: () = {
			#[allow(unused)]
			type __hidden_use_of_unchecked_extrinsic = #unchecked_extrinsic;
		};

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
	module_declarations: impl Iterator<Item = &'a Module>,
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
	module_declarations: impl Iterator<Item = &'a Module>,
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
	module_declarations: impl Iterator<Item = &'a Module>,
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
		#scrate::impl_outer_config! {
			pub struct GenesisConfig for #runtime where AllModulesWithSystem = AllModulesWithSystem {
				#(#modules_tokens)*
			}
		}
	)
}

fn decl_runtime_metadata<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a Module>,
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

			let index = module_declaration.index;

			quote!(
				#module::Module #(#instance)* as #name { index #index } with #(#filtered_names)*,
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
	module_declarations: impl Iterator<Item = &'a Module>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter(|module_declaration| module_declaration.exists_part("Call"))
		.map(|module_declaration| {
			let module = &module_declaration.module;
			let name = &module_declaration.name;
			let index = module_declaration.index.to_string();
			quote!(#[codec(index = #index)] #module::#name)
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
	modules_except_system: impl Iterator<Item = &'a Module>,
	system_module: &'a Module,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
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
				let index = module_declaration.index.to_string();
				let tokens = quote!(#[codec(index = #index)] #module #instance #generics,);
				modules_tokens.extend(tokens);
			}
			None => {}
		}
	}

	let system_name = &system_module.module;
	let system_index = system_module.index.to_string();

	Ok(quote!(
		#scrate::impl_outer_origin! {
			pub enum Origin for #runtime_name where
				system = #system_name,
				system_index = #system_index
			{
				#modules_tokens
			}
		}
	))
}

fn decl_outer_event<'a>(
	runtime_name: &'a Ident,
	module_declarations: impl Iterator<Item = &'a Module>,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
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

				let index = module_declaration.index.to_string();
				let tokens = quote!(#[codec(index = #index)] #module #instance #generics,);
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
	module_declarations: impl Iterator<Item = &'a Module>,
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

	let all_modules_with_system = names.iter()
		.fold(TokenStream2::default(), |combined, name| quote!((#name, #combined)));

	quote!(
		#types
		type AllModules = ( #all_modules );
		type AllModulesWithSystem = ( #all_modules_with_system );
	)
}

fn decl_pallet_runtime_setup(
	module_declarations: &[Module],
	scrate: &TokenStream2,
) -> TokenStream2 {
	let names = module_declarations.iter().map(|d| &d.name);
	let names2 = module_declarations.iter().map(|d| &d.name);
	let name_strings = module_declarations.iter().map(|d| d.name.to_string());
	let indices = module_declarations.iter()
		.map(|module| module.index as usize);

	quote!(
		/// Provides an implementation of `PalletInfo` to provide information
		/// about the pallet setup in the runtime.
		pub struct PalletInfo;

		impl #scrate::traits::PalletInfo for PalletInfo {
			fn index<P: 'static>() -> Option<usize> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					if type_id == #scrate::sp_std::any::TypeId::of::<#names>() {
						return Some(#indices)
					}
				)*

				None
			}

			fn name<P: 'static>() -> Option<&'static str> {
				let type_id = #scrate::sp_std::any::TypeId::of::<P>();
				#(
					if type_id == #scrate::sp_std::any::TypeId::of::<#names2>() {
						return Some(#name_strings)
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
