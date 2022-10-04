// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Checks the trait declaration, makes the trait declaration module local, removes all method
//! default implementations and implements the trait for `&mut dyn Externalities`.

use crate::utils::{
	create_function_ident_with_version, generate_crate_access,
	get_function_argument_types_without_ref, get_runtime_interface,
};

use syn::{
	fold::{self, Fold},
	spanned::Spanned,
	Error, Generics, ItemTrait, Receiver, Result, TraitItemMethod, Type, Visibility,
};

use proc_macro2::TokenStream;

use quote::quote;

/// Process the given trait definition, by checking that the definition is valid, fold it to the
/// essential definition and implement this essential definition for `dyn Externalities`.
pub fn process(trait_def: &ItemTrait, is_wasm_only: bool) -> Result<TokenStream> {
	let impl_trait = impl_trait_for_externalities(trait_def, is_wasm_only)?;
	let essential_trait_def = declare_essential_trait(trait_def)?;

	Ok(quote! {
		#impl_trait

		#essential_trait_def
	})
}

/// Converts the given trait definition into the essential trait definition without method
/// default implementations and visibility set to inherited.
struct ToEssentialTraitDef {
	/// All errors found while doing the conversion.
	errors: Vec<Error>,
	methods: Vec<TraitItemMethod>,
}

impl ToEssentialTraitDef {
	fn new() -> Self {
		ToEssentialTraitDef { errors: vec![], methods: vec![] }
	}

	fn into_methods(self) -> Result<Vec<TraitItemMethod>> {
		let mut errors = self.errors;
		let methods = self.methods;
		if let Some(first_error) = errors.pop() {
			Err(errors.into_iter().fold(first_error, |mut o, n| {
				o.combine(n);
				o
			}))
		} else {
			Ok(methods)
		}
	}

	fn process(&mut self, method: &TraitItemMethod, version: u32) {
		let mut folded = self.fold_trait_item_method(method.clone());
		folded.sig.ident = create_function_ident_with_version(&folded.sig.ident, version);
		self.methods.push(folded);
	}

	fn push_error<S: Spanned>(&mut self, span: &S, msg: &str) {
		self.errors.push(Error::new(span.span(), msg));
	}

	fn error_on_generic_parameters(&mut self, generics: &Generics) {
		if let Some(param) = generics.params.first() {
			self.push_error(param, "Generic parameters not supported.");
		}
	}
}

impl Fold for ToEssentialTraitDef {
	fn fold_trait_item_method(&mut self, mut method: TraitItemMethod) -> TraitItemMethod {
		if method.default.take().is_none() {
			self.push_error(&method, "Methods need to have an implementation.");
		}

		let arg_types = get_function_argument_types_without_ref(&method.sig);
		arg_types
			.filter_map(|ty| match *ty {
				Type::ImplTrait(impl_trait) => Some(impl_trait),
				_ => None,
			})
			.for_each(|invalid| self.push_error(&invalid, "`impl Trait` syntax not supported."));

		self.error_on_generic_parameters(&method.sig.generics);

		method.attrs.retain(|a| !a.path.is_ident("version"));

		fold::fold_trait_item_method(self, method)
	}

	fn fold_item_trait(&mut self, mut trait_def: ItemTrait) -> ItemTrait {
		self.error_on_generic_parameters(&trait_def.generics);

		trait_def.vis = Visibility::Inherited;
		fold::fold_item_trait(self, trait_def)
	}

	fn fold_receiver(&mut self, receiver: Receiver) -> Receiver {
		if receiver.reference.is_none() {
			self.push_error(&receiver, "Taking `Self` by value is not allowed.");
		}

		fold::fold_receiver(self, receiver)
	}
}

fn declare_essential_trait(trait_def: &ItemTrait) -> Result<TokenStream> {
	let trait_ = &trait_def.ident;

	if let Some(param) = trait_def.generics.params.first() {
		return Err(Error::new(param.span(), "Generic parameters not supported."))
	}

	let interface = get_runtime_interface(trait_def)?;
	let mut folder = ToEssentialTraitDef::new();
	for (version, interface_method) in interface.all_versions() {
		folder.process(interface_method, version);
	}
	let methods = folder.into_methods()?;

	Ok(quote! {
		trait #trait_ {
			#( #methods )*
		}
	})
}

/// Implements the given trait definition for `dyn Externalities`.
fn impl_trait_for_externalities(trait_def: &ItemTrait, is_wasm_only: bool) -> Result<TokenStream> {
	let trait_ = &trait_def.ident;
	let crate_ = generate_crate_access();
	let interface = get_runtime_interface(trait_def)?;
	let methods = interface.all_versions().map(|(version, method)| {
		let mut cloned = method.clone();
		cloned.attrs.retain(|a| !a.path.is_ident("version"));
		cloned.sig.ident = create_function_ident_with_version(&cloned.sig.ident, version);
		cloned
	});

	let impl_type = if is_wasm_only {
		quote!( &mut dyn #crate_::sp_wasm_interface::FunctionContext )
	} else {
		quote!( &mut dyn #crate_::Externalities )
	};

	Ok(quote! {
		#[cfg(feature = "std")]
		impl #trait_ for #impl_type {
			#( #methods )*
		}
	})
}
