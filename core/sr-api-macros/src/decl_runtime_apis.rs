// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

use crate::utils::{
	generate_crate_access, generate_hidden_includes, generate_runtime_mod_name_for_trait,
	fold_fn_decl_for_client_side, unwrap_or_error, extract_parameter_names_types_and_borrows,
	generate_native_call_generator_fn_name, return_type_extract_type,
	generate_method_runtime_api_impl_name, generate_call_api_at_fn_name, prefix_function_with_trait,
};

use proc_macro2::{TokenStream, Span};

use quote::quote;

use syn::{
	spanned::Spanned, parse_macro_input, parse::{Parse, ParseStream, Result, Error}, ReturnType,
	fold::{self, Fold}, parse_quote, ItemTrait, Generics, GenericParam, Attribute, FnArg,
	visit::{Visit, self}, Pat, TraitBound, Meta, NestedMeta, Lit, TraitItem, Ident, Type,
	TraitItemMethod
};

use std::collections::HashMap;

use blake2_rfc;

/// The ident used for the block generic parameter.
const BLOCK_GENERIC_IDENT: &str = "Block";

/// Unique identifier used to make the hidden includes unique for this macro.
const HIDDEN_INCLUDES_ID: &str = "DECL_RUNTIME_APIS";

/// The `core_trait` attribute.
const CORE_TRAIT_ATTRIBUTE: &str = "core_trait";
/// The `api_version` attribute.
///
/// Is used to set the current version of the trait.
const API_VERSION_ATTRIBUTE: &str = "api_version";
/// The `changed_in` attribute.
///
/// Is used when the function signature changed between different versions of a trait.
/// This attribute should be placed on the old signature of the function.
const CHANGED_IN_ATTRIBUTE: &str = "changed_in";
/// The `renamed` attribute.
///
/// Is used when a trait method was renamed.
const RENAMED_ATTRIBUTE: &str = "renamed";
/// The `skip_initialize_block` attribute.
///
/// Is used when a trait method does not require that the block is initialized
/// before being called.
const SKIP_INITIALIZE_BLOCK_ATTRIBUTE: &str = "skip_initialize_block";
/// The `initialize_block` attribute.
///
/// A trait method tagged with this attribute, initializes the runtime at
/// certain block.
const INITIALIZE_BLOCK_ATTRIBUTE: &str = "initialize_block";
/// All attributes that we support in the declaration of a runtime api trait.
const SUPPORTED_ATTRIBUTE_NAMES: &[&str] = &[
	CORE_TRAIT_ATTRIBUTE, API_VERSION_ATTRIBUTE, CHANGED_IN_ATTRIBUTE,
	RENAMED_ATTRIBUTE, SKIP_INITIALIZE_BLOCK_ATTRIBUTE,
	INITIALIZE_BLOCK_ATTRIBUTE,
];

/// The structure used for parsing the runtime api declarations.
struct RuntimeApiDecls {
	decls: Vec<ItemTrait>,
}

impl Parse for RuntimeApiDecls {
	fn parse(input: ParseStream) -> Result<Self> {
		let mut decls = Vec::new();

		while !input.is_empty() {
			decls.push(ItemTrait::parse(input)?);
		}

		Ok(Self { decls })
	}
}

/// Extend the given generics with `Block: BlockT` as first generic parameter.
fn extend_generics_with_block(generics: &mut Generics) {
	let c = generate_crate_access(HIDDEN_INCLUDES_ID);

	generics.lt_token = Some(parse_quote!(<));
	generics.params.insert(0, parse_quote!( Block: #c::runtime_api::BlockT ));
	generics.gt_token = Some(parse_quote!(>));
}

/// Remove all attributes from the vector that are supported by us in the declaration of a runtime
/// api trait. The returned hashmap contains all found attribute names as keys and the rest of the
/// attribute body as `TokenStream`.
fn remove_supported_attributes(attrs: &mut Vec<Attribute>) -> HashMap<&'static str, Attribute> {
	let mut result = HashMap::new();
	attrs.retain(|v| {
		match SUPPORTED_ATTRIBUTE_NAMES.iter().find(|a| v.path.is_ident(a)) {
			Some(attribute) => {
				result.insert(*attribute, v.clone());
				false
			},
			None => true,
		}
	});

	result
}

/// Visits the ast and checks if `Block` ident is used somewhere.
struct IsUsingBlock {
	result: bool,
}

impl<'ast> Visit<'ast> for IsUsingBlock {
	fn visit_ident(&mut self, i: &'ast Ident) {
		if i == BLOCK_GENERIC_IDENT {
			self.result = true;
		}
	}
}

/// Visits the ast and checks if `Block` ident is used somewhere.
fn type_is_using_block(ty: &Type) -> bool {
	let mut visitor = IsUsingBlock { result: false };
	visitor.visit_type(ty);
	visitor.result
}

/// Visits the ast and checks if `Block` ident is used somewhere.
fn return_type_is_using_block(ty: &ReturnType) -> bool {
	let mut visitor = IsUsingBlock { result: false };
	visitor.visit_return_type(ty);
	visitor.result
}

/// Replace all occurrences of `Block` with `NodeBlock`
struct ReplaceBlockWithNodeBlock {}

impl Fold for ReplaceBlockWithNodeBlock {
	fn fold_ident(&mut self, input: Ident) -> Ident {
		if input == BLOCK_GENERIC_IDENT {
			Ident::new("NodeBlock", Span::call_site())
		} else {
			input
		}
	}
}

/// Replace all occurrences of `Block` with `NodeBlock`
fn fn_arg_replace_block_with_node_block(fn_arg: FnArg) -> FnArg {
	let mut replace = ReplaceBlockWithNodeBlock {};
	fold::fold_fn_arg(&mut replace, fn_arg)
}

/// Replace all occurrences of `Block` with `NodeBlock`
fn return_type_replace_block_with_node_block(return_type: ReturnType) -> ReturnType {
	let mut replace = ReplaceBlockWithNodeBlock {};
	fold::fold_return_type(&mut replace, return_type)
}

/// Generate the functions that generate the native call closure for each trait method.
fn generate_native_call_generators(decl: &ItemTrait) -> Result<TokenStream> {
	let fns = decl.items.iter().filter_map(|i| match i {
		TraitItem::Method(ref m) => Some(&m.sig),
		_ => None,
	});

	let mut result = Vec::new();
	let trait_ = &decl.ident;
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	// Auxiliary function that is used to convert between types that use different block types.
	// The function expects that both a convertable by encoding the one and decoding the other.
	result.push(quote!(
		#[cfg(any(feature = "std", test))]
		fn convert_between_block_types
			<I: #crate_::runtime_api::Encode, R: #crate_::runtime_api::Decode>(
				input: &I, error_desc: &'static str,
			) -> ::std::result::Result<R, &'static str>
		{
			<R as #crate_::runtime_api::Decode>::decode(
				&mut &#crate_::runtime_api::Encode::encode(input)[..]
			).ok_or_else(|| error_desc)
		}
	));

	// Generate a native call generator for each function of the given trait.
	for fn_ in fns {
		let params = extract_parameter_names_types_and_borrows(&fn_.decl)?;
		let trait_fn_name = &fn_.ident;
		let fn_name = generate_native_call_generator_fn_name(&fn_.ident);
		let output = return_type_replace_block_with_node_block(fn_.decl.output.clone());
		let output_ty = return_type_extract_type(&output);
		let output = quote!( ::std::result::Result<#output_ty, &'static str> );

		// Every type that is using the `Block` generic parameter, we need to encode/decode,
		// to make it compatible between the runtime/node.
		let conversions = params.iter().filter(|v| type_is_using_block(&v.1)).map(|(n, t, _)| {
			let name_str = format!(
				"Could not convert parameter `{}` between node and runtime!", quote!(#n)
			);
			quote!(
				let #n: #t = convert_between_block_types(&#n, #name_str)?;
			)
		});
		// Same as for the input types, we need to check if we also need to convert the output,
		// before returning it.
		let output_conversion = if return_type_is_using_block(&fn_.decl.output) {
			quote!(
				convert_between_block_types(
					&res,
					"Could not convert return value from runtime to node!"
				)
			)
		} else {
			quote!( Ok(res) )
		};

		let input_names = params.iter().map(|v| &v.0);
		// If the type is using the block generic type, we will encode/decode it to make it
		// compatible. To ensure that we forward it by ref/value, we use the value given by the
		// the user. Otherwise if it is not using the block, we don't need to add anything.
		let input_borrows = params
			.iter()
			.map(|v| if type_is_using_block(&v.1) { v.2.clone() } else { quote!() });

		// Replace all `Block` with `NodeBlock`, add `'a` lifetime to references and collect
		// all the function inputs.
		let fn_inputs = fn_
			.decl
			.inputs
			.iter()
			.map(|v| fn_arg_replace_block_with_node_block(v.clone()))
			.map(|v| match v {
				FnArg::Captured(ref arg) => {
					let mut arg = arg.clone();
					if let Type::Reference(ref mut r) = arg.ty {
						r.lifetime = Some(parse_quote!( 'a ));
					}
					FnArg::Captured(arg)
				},
				r => r.clone(),
			});

		let (impl_generics, ty_generics, where_clause) = decl.generics.split_for_impl();
		// We need to parse them again, to get an easy access to the actual parameters.
		let impl_generics: Generics = parse_quote!( #impl_generics );
		let impl_generics_params = impl_generics.params.iter().map(|p| {
			match p {
				GenericParam::Type(ref ty) => {
					let mut ty = ty.clone();
					ty.bounds.push(parse_quote!( 'a ));
					GenericParam::Type(ty)
				},
				// We should not see anything different than type params here.
				r => r.clone(),
			}
		});

		// Generate the generator function
		result.push(quote!(
			#[cfg(any(feature = "std", test))]
			pub fn #fn_name<
				'a, ApiImpl: #trait_ #ty_generics, NodeBlock: #crate_::runtime_api::BlockT
				#(, #impl_generics_params)*
			>(
				#( #fn_inputs ),*
			) -> impl FnOnce() -> #output + 'a #where_clause {
				move || {
					#( #conversions )*
					let res = ApiImpl::#trait_fn_name(#( #input_borrows #input_names ),*);
					#output_conversion
				}
			}
		));
	}

	Ok(quote!( #( #result )* ))
}

/// Try to parse the given `Attribute` as `renamed` attribute.
fn parse_renamed_attribute(renamed: &Attribute) -> Result<(String, u32)> {
	let meta = renamed.parse_meta()?;

	let err = Err(Error::new(
			meta.span(),
			&format!(
				"Unexpected `{renamed}` attribute. The supported format is `{renamed}(\"old_name\", version_it_was_renamed)`",
				renamed = RENAMED_ATTRIBUTE,
			)
		)
	);

	match meta {
		Meta::List(list) => {
			if list.nested.len() > 2 && list.nested.is_empty() {
				err
			} else {
				let mut itr = list.nested.iter();
				let old_name = match itr.next() {
					Some(NestedMeta::Literal(Lit::Str(i))) => {
						i.value()
					},
					_ => return err,
				};

				let version = match itr.next() {
					Some(NestedMeta::Literal(Lit::Int(i))) => {
						i.value() as u32
					},
					_ => return err,
				};

				Ok((old_name, version))
			}
		},
		_ => err,
	}
}

/// Generate the functions that call the api at a given block for a given trait method.
fn generate_call_api_at_calls(decl: &ItemTrait) -> Result<TokenStream> {
	let fns = decl.items.iter().filter_map(|i| match i {
		TraitItem::Method(ref m) => Some((&m.attrs, &m.sig)),
		_ => None,
	});

	let mut result = Vec::new();
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);

	// Generate a native call generator for each function of the given trait.
	for (attrs, fn_) in fns {
		let trait_name = &decl.ident;
		let trait_fn_name = prefix_function_with_trait(&trait_name, &fn_.ident);
		let fn_name = generate_call_api_at_fn_name(&fn_.ident);

		let attrs = remove_supported_attributes(&mut attrs.clone());

		if attrs.contains_key(RENAMED_ATTRIBUTE) && attrs.contains_key(CHANGED_IN_ATTRIBUTE) {
			return Err(Error::new(
				fn_.span(),
				format!(
					"`{}` and `{}` are not supported at once.",
					RENAMED_ATTRIBUTE,
					CHANGED_IN_ATTRIBUTE
				)
			));
		}

		// We do not need to generate this function for a method that signature was changed.
		if attrs.contains_key(CHANGED_IN_ATTRIBUTE) {
			continue;
		}

		let skip_initialize_block = attrs.contains_key(SKIP_INITIALIZE_BLOCK_ATTRIBUTE);
		let update_initialized_block = if attrs.contains_key(INITIALIZE_BLOCK_ATTRIBUTE) {
			quote!(
				|| *initialized_block.borrow_mut() = Some(*at)
			)
		} else {
			quote!(|| ())
		};

		// Parse the renamed attributes.
		let mut renames = Vec::new();
		if let Some((_, a)) = attrs
			.iter()
			.find(|a| a.0 == &RENAMED_ATTRIBUTE)
		{
			let (old_name, version) = parse_renamed_attribute(a)?;
			renames.push((version, prefix_function_with_trait(&trait_name, &old_name)));
		}

		renames.sort_unstable_by(|l, r| r.cmp(l));
		let (versions, old_names) = renames.into_iter().fold(
			(Vec::new(), Vec::new()),
			|(mut versions, mut old_names), (version, old_name)| {
				versions.push(version);
				old_names.push(old_name);
				(versions, old_names)
			}
		);

		// Generate the generator function
		result.push(quote!(
			#[cfg(any(feature = "std", test))]
			pub fn #fn_name<
				R: #crate_::runtime_api::Encode + #crate_::runtime_api::Decode + PartialEq,
				NC: FnOnce() -> ::std::result::Result<R, &'static str> + ::std::panic::UnwindSafe,
				Block: #crate_::runtime_api::BlockT,
				T: #crate_::runtime_api::CallRuntimeAt<Block>,
				C: #crate_::runtime_api::Core<Block>,
			>(
				call_runtime_at: &T,
				core_api: &C,
				at: &#crate_::runtime_api::BlockId<Block>,
				args: Vec<u8>,
				changes: &std::cell::RefCell<#crate_::runtime_api::OverlayedChanges>,
				initialized_block: &std::cell::RefCell<Option<#crate_::runtime_api::BlockId<Block>>>,
				native_call: Option<NC>,
				context: #crate_::runtime_api::ExecutionContext,
				recorder: &Option<std::rc::Rc<std::cell::RefCell<#crate_::runtime_api::ProofRecorder<Block>>>>,
			) -> #crate_::error::Result<#crate_::runtime_api::NativeOrEncoded<R>> {
				let version = call_runtime_at.runtime_version_at(at)?;
				use #crate_::runtime_api::InitializeBlock;
				let initialize_block = if #skip_initialize_block {
					InitializeBlock::Skip
				} else {
					InitializeBlock::Do(&initialized_block)
				};
				let update_initialized_block = #update_initialized_block;

				#(
					// Check if we need to call the function by an old name.
					if version.apis.iter().any(|(s, v)| {
						s == &ID && *v < #versions
					}) {
						let ret = call_runtime_at.call_api_at::<R, fn() -> _, _>(
							core_api,
							at,
							#old_names,
							args,
							changes,
							initialize_block,
							None,
							context,
							recorder,
						)?;

						update_initialized_block();
						return Ok(ret);
					}
				)*

				let ret = call_runtime_at.call_api_at(
					core_api,
					at,
					#trait_fn_name,
					args,
					changes,
					initialize_block,
					native_call,
					context,
					recorder,
				)?;

				update_initialized_block();
				Ok(ret)
			}
		));
	}

	Ok(quote!( #( #result )* ))
}

/// Generate the declaration of the trait for the runtime.
fn generate_runtime_decls(decls: &[ItemTrait]) -> TokenStream {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();
		extend_generics_with_block(&mut decl.generics);
		let mod_name = generate_runtime_mod_name_for_trait(&decl.ident);
		let found_attributes = remove_supported_attributes(&mut decl.attrs);
		let api_version = unwrap_or_error(get_api_version(&found_attributes).map(|v| {
			generate_runtime_api_version(v as u32)
		}));
		let id = generate_runtime_api_id(&decl.ident.to_string());

		let call_api_at_calls = unwrap_or_error(generate_call_api_at_calls(&decl));

		// Remove methods that have the `changed_in` attribute as they are not required for the
		// runtime anymore.
		decl.items = decl.items.iter_mut().filter_map(|i| match i {
			TraitItem::Method(ref mut method) => {
				if remove_supported_attributes(&mut method.attrs).contains_key(CHANGED_IN_ATTRIBUTE) {
					None
				} else {
					Some(TraitItem::Method(method.clone()))
				}
			}
			r => Some(r.clone()),
		}).collect();

		let native_call_generators = unwrap_or_error(generate_native_call_generators(&decl));

		result.push(quote!(
			#[doc(hidden)]
			#[allow(dead_code)]
			#[allow(deprecated)]
			pub mod #mod_name {
				use super::*;

				#decl

				pub #api_version

				pub #id

				#native_call_generators

				#call_api_at_calls
			}
		));
	}

	quote!( #( #result )* )
}

/// Modify the given runtime api declaration to be usable on the client side.
struct ToClientSideDecl<'a> {
	block_id: &'a TokenStream,
	crate_: &'a TokenStream,
	found_attributes: &'a mut HashMap<&'static str, Attribute>,
	/// Any error that we found while converting this declaration.
	errors: &'a mut Vec<TokenStream>,
	trait_: &'a Ident,
}

impl<'a> ToClientSideDecl<'a> {
	fn fold_item_trait_items(&mut self, items: Vec<TraitItem>) -> Vec<TraitItem> {
		let mut result = Vec::new();

		items.into_iter().for_each(|i| match i {
			TraitItem::Method(method) => {
				let (fn_decl, fn_impl, fn_decl_ctx) = self.fold_trait_item_method(method);
				result.push(fn_decl.into());
				result.push(fn_decl_ctx.into());

				if let Some(fn_impl) = fn_impl {
					result.push(fn_impl.into());
				}
			},
			r => result.push(r),
		});

		result
	}

	fn fold_trait_item_method(&mut self, method: TraitItemMethod)
		-> (TraitItemMethod, Option<TraitItemMethod>, TraitItemMethod) {
		let crate_ = self.crate_;
		let context_other = quote!( #crate_::runtime_api::ExecutionContext::Other );
		let fn_impl = self.create_method_runtime_api_impl(method.clone());
		let fn_decl = self.create_method_decl(method.clone(), context_other);
		let fn_decl_ctx = self.create_method_decl_with_context(method);

		(fn_decl, fn_impl, fn_decl_ctx)
	}

	fn create_method_decl_with_context(&mut self, method: TraitItemMethod) -> TraitItemMethod {
		let crate_ = self.crate_;
		let context_arg: syn::FnArg = parse_quote!( context: #crate_::runtime_api::ExecutionContext );
		let mut fn_decl_ctx = self.create_method_decl(method, quote!( context ));
		fn_decl_ctx.sig.ident = Ident::new(&format!("{}_with_context", &fn_decl_ctx.sig.ident), Span::call_site());
		fn_decl_ctx.sig.decl.inputs.insert(2, context_arg);

		fn_decl_ctx
	}

	/// Takes the given method and creates a `method_runtime_api_impl` method that will be
	/// implemented in the runtime for the client side.
	fn create_method_runtime_api_impl(&mut self, mut method: TraitItemMethod) -> Option<TraitItemMethod> {
		if remove_supported_attributes(&mut method.attrs).contains_key(CHANGED_IN_ATTRIBUTE) {
			return None;
		}

		let fn_decl = &method.sig.decl;
		let ret_type = return_type_extract_type(&fn_decl.output);

		// Get types and if the value is borrowed from all parameters.
		// If there is an error, we push it as the block to the user.
		let param_types = match extract_parameter_names_types_and_borrows(fn_decl) {
			Ok(res) => res.into_iter().map(|v| {
				let ty = v.1;
				let borrow = v.2;
				quote!( #borrow #ty )
			}).collect::<Vec<_>>(),
			Err(e) => {
				self.errors.push(e.to_compile_error());
				Vec::new()
			}
		};
		let name = generate_method_runtime_api_impl_name(&self.trait_, &method.sig.ident);
		let block_id = self.block_id;
		let crate_ = self.crate_;

		Some(
			parse_quote!{
				#[doc(hidden)]
				fn #name(
					&self,
					at: &#block_id,
					context: #crate_::runtime_api::ExecutionContext,
					params: Option<( #( #param_types ),* )>,
					params_encoded: Vec<u8>,
				) -> #crate_::error::Result<#crate_::runtime_api::NativeOrEncoded<#ret_type>>;
			}
		)
	}

	/// Takes the method declared by the user and creates the declaration we require for the runtime
	/// api client side. This method will call by default the `method_runtime_api_impl` for doing
	/// the actual call into the runtime.
	fn create_method_decl(&mut self, mut method: TraitItemMethod, context: TokenStream) -> TraitItemMethod {
		let params = match extract_parameter_names_types_and_borrows(&method.sig.decl) {
			Ok(res) => res.into_iter().map(|v| v.0).collect::<Vec<_>>(),
			Err(e) => {
				self.errors.push(e.to_compile_error());
				Vec::new()
			}
		};
		let params2 = params.clone();
		let ret_type = return_type_extract_type(&method.sig.decl.output);

		method.sig.decl = fold_fn_decl_for_client_side(
			method.sig.decl.clone(),
			&self.block_id,
			&self.crate_
		);
		let name_impl = generate_method_runtime_api_impl_name(&self.trait_, &method.sig.ident);
		let crate_ = self.crate_;

		let found_attributes = remove_supported_attributes(&mut method.attrs);
		// If the method has a `changed_in` attribute, we need to alter the method name to
		// `method_before_version_VERSION`.
		let (native_handling, param_tuple) = match get_changed_in(&found_attributes) {
			Ok(Some(version)) => {
				// Make sure that the `changed_in` version is at least the current `api_version`.
				if get_api_version(&self.found_attributes).ok() < Some(version) {
					self.errors.push(
						Error::new(
							method.span(),
							"`changed_in` version can not be greater than the `api_version`",
						).to_compile_error()
					);
				}

				let ident = Ident::new(
					&format!("{}_before_version_{}", method.sig.ident, version),
					method.sig.ident.span()
				);
				method.sig.ident = ident;
				method.attrs.push(parse_quote!( #[deprecated] ));

				let panic = format!("Calling `{}` should not return a native value!", method.sig.ident);
				(quote!( panic!(#panic) ), quote!( None ))
			},
			Ok(None) => (quote!( Ok(n) ), quote!( Some(( #( #params2 ),* )) )),
			Err(e) => {
				self.errors.push(e.to_compile_error());
				(quote!( unimplemented!() ), quote!( None ))
			}
		};

		let function_name = method.sig.ident.to_string();

		// Generate the default implementation that calls the `method_runtime_api_impl` method.
		method.default = Some(
			parse_quote! {
				{
					let runtime_api_impl_params_encoded =
						#crate_::runtime_api::Encode::encode(&( #( &#params ),* ));

					self.#name_impl(at, #context, #param_tuple, runtime_api_impl_params_encoded)
						.and_then(|r|
							match r {
								#crate_::runtime_api::NativeOrEncoded::Native(n) => {
									#native_handling
								},
								#crate_::runtime_api::NativeOrEncoded::Encoded(r) => {
									<#ret_type as #crate_::runtime_api::Decode>::decode(&mut &r[..])
										.ok_or_else(||
											#crate_::error::Error::CallResultDecode(
												#function_name
											).into()
										)
								}
							}
						)
				}
			}
		);

		method
	}
}

impl<'a> Fold for ToClientSideDecl<'a> {
	fn fold_item_trait(&mut self, mut input: ItemTrait) -> ItemTrait {
		extend_generics_with_block(&mut input.generics);

		*self.found_attributes = remove_supported_attributes(&mut input.attrs);
		// Check if this is the `Core` runtime api trait.
		let is_core_trait = self.found_attributes.contains_key(CORE_TRAIT_ATTRIBUTE);
		let block_ident = Ident::new(BLOCK_GENERIC_IDENT, Span::call_site());

		if is_core_trait {
			// Add all the supertraits we want to have for `Core`.
			let crate_ = &self.crate_;
			input.supertraits = parse_quote!(
				'static
				+ Send
				+ Sync
				+ #crate_::runtime_api::ApiExt<#block_ident>
			);
		} else {
			// Add the `Core` runtime api as super trait.
			let crate_ = &self.crate_;
			input.supertraits.push(parse_quote!( #crate_::runtime_api::Core<#block_ident> ));
		}

		// The client side trait is only required when compiling with the feature `std` or `test`.
		input.attrs.push(parse_quote!( #[cfg(any(feature = "std", test))] ));
		input.items = self.fold_item_trait_items(input.items);

		fold::fold_item_trait(self, input)
	}
}

/// Parse the given attribute as `API_VERSION_ATTRIBUTE`.
fn parse_runtime_api_version(version: &Attribute) -> Result<u64> {
	let meta = version.parse_meta()?;

	let err = Err(Error::new(
			meta.span(),
			&format!(
				"Unexpected `{api_version}` attribute. The supported format is `{api_version}(1)`",
				api_version = API_VERSION_ATTRIBUTE
			)
		)
	);

	match meta {
		Meta::List(list) => {
			if list.nested.len() > 1 && list.nested.is_empty() {
				err
			} else {
				match list.nested.first().as_ref().map(|v| v.value()) {
					Some(NestedMeta::Literal(Lit::Int(i))) => {
						Ok(i.value())
					},
					_ => err,
				}
			}
		},
		_ => err,
	}
}

/// Generates the identifier as const variable for the given `trait_name`
/// by hashing the `trait_name`.
fn generate_runtime_api_id(trait_name: &str) -> TokenStream {
	let mut res = [0; 8];
	res.copy_from_slice(blake2_rfc::blake2b::blake2b(8, &[], trait_name.as_bytes()).as_bytes());

	quote!(	const ID: [u8; 8] = [ #( #res ),* ]; )
}

/// Generates the const variable that holds the runtime api version.
fn generate_runtime_api_version(version: u32) -> TokenStream {
	quote!( const VERSION: u32 = #version; )
}

/// Generates the implementation of `RuntimeApiInfo` for the given trait.
fn generate_runtime_info_impl(trait_: &ItemTrait, version: u64) -> TokenStream {
	let trait_name = &trait_.ident;
	let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
	let id = generate_runtime_api_id(&trait_name.to_string());
	let version = generate_runtime_api_version(version as u32);
	let (impl_generics, ty_generics, where_clause) = trait_.generics.split_for_impl();

	quote!(
		#[cfg(any(feature = "std", test))]
		impl #impl_generics #crate_::runtime_api::RuntimeApiInfo
			for #trait_name #ty_generics #where_clause
		{
			#id
			#version
		}
	)
}

/// Get changed in version from the user given attribute or `Ok(None)`, if no attribute was given.
fn get_changed_in(found_attributes: &HashMap<&'static str, Attribute>) -> Result<Option<u64>> {
	found_attributes.get(&CHANGED_IN_ATTRIBUTE)
		.map(|v| parse_runtime_api_version(v).map(Some))
		.unwrap_or(Ok(None))
}

/// Get the api version from the user given attribute or `Ok(1)`, if no attribute was given.
fn get_api_version(found_attributes: &HashMap<&'static str, Attribute>) -> Result<u64> {
	found_attributes.get(&API_VERSION_ATTRIBUTE).map(parse_runtime_api_version).unwrap_or(Ok(1))
}

/// Generate the declaration of the trait for the client side.
fn generate_client_side_decls(decls: &[ItemTrait]) -> TokenStream {
	let mut result = Vec::new();

	for decl in decls {
		let decl = decl.clone();

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
		let block_id = quote!( #crate_::runtime_api::BlockId<Block> );
		let mut found_attributes = HashMap::new();
		let mut errors = Vec::new();
		let trait_ = decl.ident.clone();

		let decl = {
			let mut to_client_side = ToClientSideDecl {
				crate_: &crate_,
				block_id: &block_id,
				found_attributes: &mut found_attributes,
				errors: &mut errors,
				trait_: &trait_,
			};
			to_client_side.fold_item_trait(decl)
		};

		let api_version = get_api_version(&found_attributes);

		let runtime_info = unwrap_or_error(
			api_version.map(|v| generate_runtime_info_impl(&decl, v))
		);

		result.push(quote!( #decl #runtime_info #( #errors )* ));
	}

	quote!( #( #result )* )
}

/// Checks that a trait declaration is in the format we expect.
struct CheckTraitDecl {
	errors: Vec<Error>,
}

impl<'ast> Visit<'ast> for CheckTraitDecl {
	fn visit_fn_arg(&mut self, input: &'ast FnArg) {
		match input {
			FnArg::Captured(ref arg) => {
				match arg.pat {
					Pat::Ident(ref pat) if pat.ident == "at" => {
						self.errors.push(
							Error::new(
								pat.span(),
								"`decl_runtime_apis!` adds automatically a parameter \
								`at: &BlockId<Block>`. Please rename/remove your parameter."
							)
						)
					},
					_ => {}
				}
			},
			FnArg::SelfRef(_) | FnArg::SelfValue(_) => {
				self.errors.push(Error::new(input.span(), "Self values are not supported."))
			}
			_ => {
				self.errors.push(
					Error::new(
						input.span(),
						"Only function arguments in the form `pat: type` are supported."
					)
				)
			}
		}

		visit::visit_fn_arg(self, input);
	}

	fn visit_generic_param(&mut self, input: &'ast GenericParam) {
		match input {
			GenericParam::Type(ty) if ty.ident == BLOCK_GENERIC_IDENT => {
				self.errors.push(
					Error::new(
						input.span(),
						"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro!"
					)
				)
			},
			_ => {}
		}

		visit::visit_generic_param(self, input);
	}

	fn visit_trait_bound(&mut self, input: &'ast TraitBound) {
		if let Some(last_ident) = input.path.segments.last().map(|v| &v.value().ident) {
			if last_ident == "BlockT" || last_ident == BLOCK_GENERIC_IDENT {
				self.errors.push(
					Error::new(
						input.span(),
						"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro! If you try to use a different trait than the \
						substrate `Block` trait, please rename it locally."
					)
				)
			}
		}

		visit::visit_trait_bound(self, input)
	}
}

/// Check that the trait declarations are in the format we expect.
fn check_trait_decls(decls: &[ItemTrait]) -> Option<TokenStream> {
	let mut checker = CheckTraitDecl { errors: Vec::new() };
	decls.iter().for_each(|decl| visit::visit_item_trait(&mut checker, &decl));

	if checker.errors.is_empty() {
		None
	} else {
		let errors = checker.errors.into_iter().map(|e| e.to_compile_error());
		Some(quote!( #( #errors )* ))
	}
}

/// The implementation of the `decl_runtime_apis!` macro.
pub fn decl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all trait declarations
	let RuntimeApiDecls { decls: api_decls } = parse_macro_input!(input as RuntimeApiDecls);

	if let Some(errors) = check_trait_decls(&api_decls) {
		return errors.into();
	}

	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let runtime_decls = generate_runtime_decls(&api_decls);
	let client_side_decls = generate_client_side_decls(&api_decls);

	quote!(
		#hidden_includes

		#runtime_decls

		#client_side_decls
	).into()
}
