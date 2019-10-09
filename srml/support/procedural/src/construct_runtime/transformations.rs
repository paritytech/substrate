use super::parse::{ModuleDeclaration, RuntimeDefinition, WhereSection, ModulePart, ModuleEntry};
use proc_macro::TokenStream;
use proc_macro2::TokenStream as TokenStream2;
use quote::quote;
use srml_support_procedural_tools::syn_ext as ext;
use syn::Ident;

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
	let outer_event = decl_outer_event(&name, modules.iter(), &system_module);
	quote!(
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub struct #name;
		impl $crate::sr_primitives::traits::GetNodeBlockType for #name {
			type NodeBlock = #node_block;
		}
		impl $crate::sr_primitives::traits::GetRuntimeBlockType for #name {
			type RuntimeBlock = #block;
		}

		#outer_event
	)
	.into()
}

fn decl_outer_event<'a>(
	runtime_name: &'a Ident,
	module_declarations: impl Iterator<Item = &'a ModuleDeclaration>,
	system_name: &'a Ident,
) -> TokenStream2 {
	quote!(
		$crate::impl_outer_event! {
			pub enum Event for #runtime_name where system = #system_name {

			}
		}
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
			},
			ModuleEntry::Part(part) => {
				if part.name == *name {
					return Some(part.clone())
				}
			},
			_ => {},
		}
	}

	None
}
