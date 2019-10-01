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

//! Generates the bare function interface for a given trait definition.

use crate::utils::{
	generate_crate_access, create_host_function_ident, get_function_arguments,
	get_function_argument_names, get_function_argument_types_without_ref, get_trait_methods,
};

use syn::{
	Ident, ItemTrait, TraitItemMethod, FnArg, Signature, Result, ReturnType, spanned::Spanned,
};

use proc_macro2::{TokenStream, Span};

use quote::{quote, quote_spanned};

/// Generate the bare-function interface.
pub fn generate(trait_def: &ItemTrait) -> Result<TokenStream> {
	let trait_name = &trait_def.ident;
	get_trait_methods(trait_def).try_fold(TokenStream::new(), |mut t, m| {
		t.extend(function_for_method(trait_name, m)?);
		Ok(t)
	})
}

/// Generates the bare function implementation for the given method.
fn function_for_method(trait_name: &Ident, method: &TraitItemMethod) -> Result<TokenStream> {
	let std_impl = function_std_impl(trait_name, method)?;
	let no_std_impl = function_no_std_impl(trait_name, method)?;
	let function_impl_name = create_function_impl_ident(&method.sig.ident);
	let function_name = &method.sig.ident;
	let args = get_function_arguments(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let return_value = &method.sig.output;
	let attrs = &method.attrs;

	Ok(
		quote! {
			#( #attrs )*
			pub fn #function_name( #( #args, )* ) #return_value {
				#std_impl

				#no_std_impl

				#function_impl_name( #( #arg_names, )* )
			}
		}
	)
}

/// Generates the bare function implementation for `cfg(not(feature = "std"))`.
fn function_no_std_impl(trait_name: &Ident, method: &TraitItemMethod) -> Result<TokenStream> {
	let function_name = create_function_impl_ident(&method.sig.ident);
	let host_function_name = create_host_function_ident(&method.sig.ident, trait_name);
	let args = get_function_arguments(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let arg_names2 = get_function_argument_names(&method.sig);
	let arg_types = get_function_argument_types_without_ref(&method.sig);
	let crate_ = generate_crate_access();
	let return_value = &method.sig.output;
	let convert_return_value = match return_value {
		ReturnType::Default => quote!(),
		ReturnType::Type(_, ref ty) => quote! {
			<#ty as #crate_::wasm::FromFFIValue>::from_ffi_value(result)
		}
	};

	Ok(
		quote! {
			#[cfg(not(feature = "std"))]
			fn #function_name( #( #args, )* ) #return_value {
				// Generate all wrapped ffi value.
				#(
					let #arg_names = <#arg_types as #crate_::wasm::IntoFFIValue>::into_ffi_value(
						&#arg_names,
					);
				)*

				// Call the host function
				let result = unsafe { #host_function_name.get()( #( #arg_names2.get(), )* ) };

				#convert_return_value
			}
		}
	)
}

/// Generates the bare function implementation for `cfg(feature = "std")`.
fn function_std_impl(trait_name: &Ident, method: &TraitItemMethod) -> Result<TokenStream> {
	let method_name = &method.sig.ident;
	let function_name = create_function_impl_ident(&method.sig.ident);
	let args = get_function_arguments(&method.sig);
	let arg_names = get_function_argument_names(&method.sig);
	let crate_ = generate_crate_access();
	let return_value = &method.sig.output;
	let expect_msg = format!(
		"`{}` called outside of an Externalities-provided environment.",
		method_name,
	);

	let call_to_trait = if takes_self_argument(&method.sig) {
		quote_spanned! { method.span() =>
			#crate_::with_externalities(
				|mut ext| #trait_name::#method_name(&mut ext, #( #arg_names, )*)
			).expect(#expect_msg)
		}
	} else {
		quote_spanned! { method.span() =>
			<&mut dyn #crate_::Externalities<#crate_::Blake2Hasher> as #trait_name>::#method_name(
				#( #arg_names, )*
			)
		}
	};

	Ok(
		quote_spanned! { method.span() =>
			#[cfg(feature = "std")]
			fn #function_name( #( #args, )* ) #return_value {
				#call_to_trait
			}
		}
	)
}

/// Create the function identifier for the internal implementation function.
fn create_function_impl_ident(method_name: &Ident) -> Ident {
	Ident::new(&format!("{}_impl", method_name), Span::call_site())
}

/// Returns if the given `Signature` takes a `self` argument.
fn takes_self_argument(sig: &Signature) -> bool {
	match sig.inputs.first() {
		Some(FnArg::Receiver(_)) => true,
		_ => false,
	}
}
