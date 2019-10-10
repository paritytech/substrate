use super::parse::{ModuleDeclaration, ModuleEntry, ModulePart, RuntimeDefinition, WhereSection};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
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
	let outer_event = try_tok!(decl_outer_event(
		&name,
		modules.iter().filter(|module| module.name.to_string() != "System"),
		&system_module,
		&scrate,
	));
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
	)
	.into();

	println!("-----\n{}\n------", res.to_string());
	res
}

fn decl_outer_event<'a>(
	runtime_name: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	system_name: &'a Ident,
	scrate: &'a TokenStream2,
) -> syn::Result<TokenStream2> {
	let mut modules_tokens = TokenStream2::new();
	for module_declaration in module_declarations {
		let event_ident = Ident::new("Event", module_declaration.name.span());
		match find_module_entry(module_declaration, &event_ident) {
			Some(module_entry) => {
				let module = &module_declaration.module;
				let instance = module_declaration
					.instance
					.inner
					.as_ref()
					.map(|instance| &instance.name);
				let generics = &module_entry.generics;
				// println!("Module `{}`, instance present: `{}`, generics present: `{}`", module, instance.is_some(), generics.inner.is_some());
				if instance.is_some() && generics.params.len() == 0 {
					let msg = format!(
						"Instantiable module with no generic `Event` cannot \
						 be constructed: module `{}` must have generic `Event`",
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
	Ok(
		quote!(
			#scrate::impl_outer_event! {
				pub enum Event for #runtime_name where system = #system_name {
					#modules_tokens
				}
			}
		)
	)
}

fn find_system_module<'a>(mut module_declarations: impl Iterator<Item = &'a ModuleDeclaration>) -> Option<&'a Ident> {
	module_declarations
		.find(|decl| decl.name.to_string().as_str() == "System")
		.map(|decl| &decl.module)
}

/// `Name` could be only one of module names included in `default` keyword
fn find_module_entry<'a>(module_declaration: &'a ModuleDeclaration, name: &'a Ident) -> Option<ModulePart> {
	let details = module_declaration.details.inner.as_ref()?;
	for entry in details.entries.content.inner.iter() {
		match &entry.inner {
			ModuleEntry::Default(default_token) => {
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
