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

//! Checks the trait declaration, folds and implements it.

use crate::utils::generate_crate_access;

use syn::{
	ItemTrait, TraitItemMethod, Result, TraitItem, Error, fold::{self, Fold}, spanned::Spanned,
	Visibility, Receiver
};

use proc_macro2::TokenStream;

use quote::quote;

/// Process the given trait definition, by checking that the definition is valid, fold and
/// implement it.
pub fn process(trait_def: &ItemTrait) -> Result<TokenStream> {
	let impl_trait = impl_trait_for_externalities(trait_def)?;
	let essential_trait_def = ToEssentialTraitDef::convert(trait_def.clone())?;

	Ok(
		quote! {
			#impl_trait

			#essential_trait_def
		}
	)
}

/// Converts the given trait definition into the essential trait definition without method
/// default implementations and visibility set to inherited.
struct ToEssentialTraitDef {
	/// All errors found while doing the conversion.
	errors: Vec<Error>,
}

impl ToEssentialTraitDef {
	/// Convert the given trait definition to the essential trait definition.
	fn convert(trait_def: ItemTrait) -> Result<ItemTrait> {
		let mut folder = ToEssentialTraitDef {
			errors: Vec::new(),
		};

		let res = fold::fold_item_trait(&mut folder, trait_def);

		if let Some(first_error) = folder.errors.pop() {
			Err(
				folder.errors.into_iter().fold(first_error, |mut o, n| {
					o.combine(n);
					o
				})
			)
		} else {
			Ok(res)
		}
	}

	fn push_error<S: Spanned>(&mut self, span: &S, msg: &str) {
		self.errors.push(Error::new(span.span(), msg));
	}
}

impl Fold for ToEssentialTraitDef {
	fn fold_trait_item_method(&mut self, mut method: TraitItemMethod) -> TraitItemMethod {
		if method.default.take().is_none() {
			self.push_error(&method, "Methods need to have an implementation");
		}

		method
	}

	fn fold_item_trait(&mut self, mut trait_def: ItemTrait) -> ItemTrait {
		if let Some(first_param) = trait_def.generics.params.first() {
			self.push_error(first_param, "Generic parameters are not supported");
		}

		trait_def.vis = Visibility::Inherited;
		trait_def
	}

	fn fold_receiver(&mut self, mut receiver: Receiver) -> Receiver {
		if receiver.reference.is_none() {
			self.push_error(&receiver, "Taking `Self` by value is not allowed");
		}

		receiver
	}
}

/// Implements the given trait definition for `dyn Externalities<Blake2Hasher>`.
fn impl_trait_for_externalities(trait_def: &ItemTrait) -> Result<TokenStream> {
	let trait_ = &trait_def.ident;
	let crate_ = generate_crate_access();
	let methods = trait_def
		.items
		.iter()
		.filter_map(|i| match i {
			TraitItem::Method(ref method) => Some(method),
			_ => None,
		});

	Ok(
		quote! {
			impl #trait_ for &mut dyn #crate_::Externalities<#crate_::Blake2Hasher> {
				#( #methods )*
			}
		}
	)
}
