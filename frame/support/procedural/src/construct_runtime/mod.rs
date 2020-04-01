// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

mod parse;

use frame_support_procedural_tools::syn_ext as ext;
use frame_support_procedural_tools::{generate_crate_access, generate_hidden_includes};
use parse::{ModuleDeclaration, RuntimeDefinition, WhereSection};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
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

	// Assert we have system module declared
	let system_module = match find_system_module(modules.iter()) {
		Some(sm) => sm,
		None => {
			return Err(syn::Error::new(
				modules_token.span,
				"`System` module declaration is missing. \
				 Please add this line: `System: system::{Module, Call, Storage, Config, Event<T>},`",
			))
		}
	};
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
		all_but_system_modules.clone(),
		&system_module,
		&scrate,
	)?;
	let all_modules = decl_all_modules(&name, modules.iter());
	let module_to_index = decl_module_to_index(modules.iter(), modules.len(), &scrate);

	let dispatch = decl_outer_dispatch(&name, modules.iter(), &scrate);
	let metadata = decl_runtime_metadata(&name, modules.iter(), &scrate, &unchecked_extrinsic);
	let outer_config = decl_outer_config(&name, modules.iter(), &scrate);
	let inherent = decl_outer_inherent(&block, &unchecked_extrinsic, modules.iter(), &scrate);
	let validate_unsigned = decl_validate_unsigned(&name, modules.iter(), &scrate);

	let res = quote!(
		#scrate_decl

		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
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
		maybe_config_part.map(|config_part| {
			let arg = config_part
				.args
				.as_ref()
				.and_then(|parens| parens.content.inner.iter().next())
				.unwrap_or(&module_declaration.name);
			let name = &module_declaration.name;
			quote!(#name : #arg,)
		})
	});
	quote!(
		#scrate::impl_outer_inherent!(
			impl Inherents where Block = #block, UncheckedExtrinsic = #unchecked_extrinsic {
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
			quote!(#module::Module #(#instance)* as #name with #(#filtered_names)* ,)
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
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter(|module_declaration| module_declaration.exists_part("Call"))
		.map(|module_declaration| {
			let module = &module_declaration.module;
			let name = &module_declaration.name;
			quote!(#module::#name)
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
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	system_name: &'a Ident,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
	for module_declaration in module_declarations {
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
				let tokens = quote!(#module #instance #generics ,);
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
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
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
				let tokens = quote!(#module #instance #generics ,);
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
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	num_modules: usize,
	scrate: &TokenStream2,
) -> TokenStream2 {
	let names = module_declarations.map(|d| &d.name);
	let indices = 0..num_modules;

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

fn find_system_module<'a>(
	mut module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
) -> Option<&'a Ident> {
	module_declarations
		.find(|decl| decl.name == SYSTEM_MODULE_NAME)
		.map(|decl| &decl.module)
}
