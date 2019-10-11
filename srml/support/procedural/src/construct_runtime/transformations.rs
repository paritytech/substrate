use super::parse::{ModuleDeclaration, ModuleEntry, ModulePart, RuntimeDefinition, WhereSection};
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
	let outer_event = try_tok!(decl_outer_event_or_origin(
		&name,
		modules.iter().filter(|module| module.name.to_string() != "System"),
		&system_module,
		&scrate,
		DeclOuterKind::Event,
	));
	let outer_origin = try_tok!(decl_outer_event_or_origin(
		&name,
		modules.iter().filter(|module| module.name.to_string() != "System"),
		&system_module,
		&scrate,
		DeclOuterKind::Origin,
	));
	let all_modules = decl_all_modules(
		&name,
		&system_module,
		modules.iter().filter(|module| module.name.to_string() != "System"),
	);

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
	)
	.into();

	println!("-----\n{}\n------", res.to_string());
	res
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
		let included_in_default = match kind {
			DeclOuterKind::Event => true,
			DeclOuterKind::Origin => false,
		};
		match find_module_entry(module_declaration, &kind_ident, included_in_default) {
			Some(module_entry) => {
				let module = &module_declaration.module;
				let instance = module_declaration
					.instance
					.inner
					.as_ref()
					.map(|instance| &instance.name);
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
	system_module: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
) -> TokenStream2 {
	let mut types = TokenStream2::new();
	let mut names = Vec::new();
	for module_declaration in module_declarations {
		let type_name = &module_declaration.name;
		let module = &module_declaration.module;
		let mut generics = vec![quote!(runtime)];
		generics.extend(module_declaration.instance.inner.iter().map(|mi| {
			let name = &mi.name;
			quote!(#module::#name)
		}));
		let type_decl = quote!(
			pub type #type_name = #module::Module <#(#generics),*>;
		);
		types.extend(type_decl);
		names.push(&module_declaration.name);
	}
	quote!(
		pub type System = system::Module<#runtime>;
		#types
		type AllModules = ( #(#names),* );
	)
}

fn find_system_module<'a>(mut module_declarations: impl Iterator<Item = &'a ModuleDeclaration>) -> Option<&'a Ident> {
	module_declarations
		.find(|decl| decl.name.to_string().as_str() == "System")
		.map(|decl| &decl.module)
}

fn find_module_entry<'a>(
	module_declaration: &'a ModuleDeclaration,
	name: &'a Ident,
	include_default: bool,
) -> Option<ModulePart> {
	let details = module_declaration.details.inner.as_ref()?;
	for entry in details.entries.content.inner.iter() {
		match &entry.inner {
			ModuleEntry::Default(default_token) => {
				if (!include_default) {
					continue;
				};
				let event_tokens = quote!(#name<T>);
				return Some(syn::parse2(event_tokens).unwrap());
			}
			ModuleEntry::Part(part) => {
				if part.name == *name {
					return Some(part.clone());
				}
			}
			_ => {}
		}
	}

	None
}
