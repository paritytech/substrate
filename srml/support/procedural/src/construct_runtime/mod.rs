// Copyright 2019 Parity Technologies (UK) Ltd.
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

use parse::{ModuleDeclaration, ModulePart, RuntimeDefinition, WhereSection};
use proc_macro::TokenStream;
use proc_macro2::{Span, TokenStream as TokenStream2};
use quote::quote;
use srml_support_procedural_tools::syn_ext as ext;
use srml_support_procedural_tools::{generate_crate_access, generate_hidden_includes};
use syn::Ident;

// try macro but returning tokenized error
macro_rules! try_tok(( $expre : expr ) => {
	match $expre {
		Ok(r) => r,
		Err (err) => {
			return err.to_compile_error().into()
		}
	}
});

pub fn construct_runtime(input: TokenStream) -> TokenStream {
	let definition = syn::parse_macro_input!(input as RuntimeDefinition);
	let RuntimeDefinition {
		name,
		where_section: WhereSection {
			block,
			node_block,
			unchecked_extrinsic,
			..
		},
		modules: ext::Braces {
			content: ext::Punctuated { inner: modules, .. },
			token: modules_token,
		},
		..
	} = definition;

	// Assert we have system module declared
	let system_module = match find_system_module(modules.iter()) {
		Some(sm) => sm,
		None => {
			return syn::Error::new(
				modules_token.span,
				"`System` module declaration is missing. \
				 Please add this line: `System: system::{Module, Call, Storage, Config, Event},`",
			)
			.to_compile_error()
			.into()
		}
	};
	let hidden_crate_name = "construct_runtime";
	let scrate = generate_crate_access(&hidden_crate_name, "srml-support");
	let scrate_decl = generate_hidden_includes(&hidden_crate_name, "srml-support");

	let all_but_system_modules = modules.iter().filter(|module| module.name != "System");

	let outer_event = try_tok!(decl_outer_event_or_origin(
		&name,
		all_but_system_modules.clone(),
		&system_module,
		&scrate,
		DeclOuterKind::Event,
	));
	let outer_origin = try_tok!(decl_outer_event_or_origin(
		&name,
		all_but_system_modules.clone(),
		&system_module,
		&scrate,
		DeclOuterKind::Origin,
	));
	let all_modules = decl_all_modules(&name, all_but_system_modules);

	let dispatch = decl_outer_dispatch(&name, modules.iter(), &scrate);
	let metadata = decl_runtime_metadata(&name, modules.iter(), &scrate);
	let outer_config = decl_outer_config(&name, modules.iter(), &scrate);
	let inherent = decl_outer_inherent(&block, &unchecked_extrinsic, modules.iter(), &scrate);
	let validate_unsigned = decl_validate_unsigned(&name, modules.iter(), &scrate);

	let res: TokenStream = quote!(
		#scrate_decl

		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct #name;
		impl #scrate::sr_primitives::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl #scrate::sr_primitives::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}

		#outer_event

		#outer_origin

		#all_modules

		#dispatch

		#metadata

		#outer_config

		#inherent

		#validate_unsigned
	)
	.into();

	res
}

fn decl_validate_unsigned<'a>(
	runtime: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	scrate: &'a TokenStream2,
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter(|module_declaration| {
			module_declaration
				.module_parts()
				.into_iter()
				.any(|part| part.name == "ValidateUnsigned")
		})
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
		let maybe_config_part = module_declaration
			.module_parts()
			.into_iter()
			.filter(|part| part.name == "Inherent")
			.next();
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
			let generics: Vec<_> = module_declaration
				.module_parts()
				.into_iter()
				.filter(|part| part.name == "Config")
				.map(|part| part.generics)
				.collect();
			if generics.len() == 0 {
				None
			} else {
				let transformed_generics: Vec<_> = generics[0].params.iter().map(|param| quote!(<#param>)).collect();
				Some((module_declaration, transformed_generics))
			}
		})
		.map(|(module_declaration, generics)| {
			let module = &module_declaration.module;
			let name = Ident::new(
				&format!("{}Config", module_declaration.name),
				module_declaration.name.span(),
			);
			let instance = module_declaration
				.instance
				.as_ref()
				.into_iter();
			quote!(
				#name =>
					#module #(#instance)* #(#generics)*,
			)
		});
	quote!(
		#scrate::sr_primitives::impl_outer_config! {
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
) -> TokenStream2 {
	let modules_tokens = module_declarations
		.filter_map(|module_declaration| {
			let parts = module_declaration.module_parts();
			let parts_len = parts.len();
			let filtered_names: Vec<_> = parts
				.into_iter()
				.filter(|part| part.name != "Module")
				.map(|part| part.name.clone())
				.collect();
			// Theres no `Module` entry
			if filtered_names.len() == parts_len {
				None
			} else {
				Some((module_declaration, filtered_names))
			}
		})
		.map(|(module_declaration, filtered_names)| {
			let module = &module_declaration.module;
			let name = &module_declaration.name;
			let instance = module_declaration
				.instance
				.as_ref()
				.map(|name| {
					quote!(<#name>)
				})
				.into_iter();
			quote!(#module::Module #(#instance)* as #name with #(#filtered_names)* ,)
		});
	quote!(
		#scrate::impl_runtime_metadata!{
			for #runtime with modules
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
		.filter(|module_declaration| {
			find_module_entry(module_declaration, &Ident::new("Call", module_declaration.name.span())).is_some()
		})
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

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum DeclOuterKind {
	Event,
	Origin,
}

fn decl_outer_event_or_origin<'a>(
	runtime_name: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	system_name: &'a Ident,
	scrate: &'a TokenStream2,
	kind: DeclOuterKind,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
	let kind_str = format!("{:?}", kind);
	for module_declaration in module_declarations {
		let kind_ident = Ident::new(kind_str.as_str(), module_declaration.name.span());
		match find_module_entry(module_declaration, &kind_ident) {
			Some(module_entry) => {
				let module = &module_declaration.module;
				let instance = module_declaration
					.instance
					.as_ref();
				let generics = &module_entry.generics;
				if instance.is_some() && generics.params.len() == 0 {
					let msg = format!(
						"Instantiable module with no generic `{}` cannot \
						 be constructed: module `{}` must have generic `{}`",
						kind_str, module_declaration.name, kind_str
					);
					return Err(syn::Error::new(module_declaration.name.span(), msg));
				}
				let tokens = quote!(#module #instance #generics ,);
				modules_tokens.extend(tokens);
			}
			None => {}
		}
	}
	let macro_call = match kind {
		DeclOuterKind::Event => quote!(#scrate::impl_outer_event!),
		DeclOuterKind::Origin => quote!(#scrate::impl_outer_origin!),
	};
	let enum_name = Ident::new(kind_str.as_str(), Span::call_site());
	Ok(quote!(
		#macro_call {
			pub enum #enum_name for #runtime_name where system = #system_name {
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
		generics.extend(module_declaration.instance.iter().map(|name| {
			quote!(#module::#name)
		}));
		let type_decl = quote!(
			pub type #type_name = #module::Module <#(#generics),*>;
		);
		types.extend(type_decl);
		names.push(&module_declaration.name);
	}
	// Make nested tuple structure like (((Babe, Consensus), Grandpa), ...)
	let all_modules = if names.len() < 2 {
		quote!(#(#names),*)
	} else {
		let name0 = names[0];
		let name1 = names[1];
		names
			.iter()
			.skip(2)
			.fold(quote!((#name0, #name1)), |acc, name| quote!((#acc, #name)))
	};
	quote!(
		pub type System = system::Module<#runtime>;
		#types
		type AllModules = ( #all_modules );
	)
}

fn find_system_module<'a>(mut module_declarations: impl Iterator<Item = &'a ModuleDeclaration>) -> Option<&'a Ident> {
	module_declarations
		.find(|decl| decl.name == "System")
		.map(|decl| &decl.module)
}

fn find_module_entry<'a>(module_declaration: &'a ModuleDeclaration, name: &'a Ident) -> Option<ModulePart> {
	let name_str = name.to_string();
	let parts = module_declaration.module_parts();
	parts.into_iter().find(|part| part.name == name_str)
}
