// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::utils::{
	extract_parameter_names_types_and_borrows, fold_fn_decl_for_client_side, generate_crate_access,
	generate_hidden_includes, generate_runtime_mod_name_for_trait, parse_runtime_api_version,
	prefix_function_with_trait, replace_wild_card_parameter_names, return_type_extract_type,
	versioned_trait_name, AllowSelfRefInParameters,
};

use crate::common::{
	API_VERSION_ATTRIBUTE, BLOCK_GENERIC_IDENT, CHANGED_IN_ATTRIBUTE, CORE_TRAIT_ATTRIBUTE,
	HIDDEN_INCLUDES_ID, RENAMED_ATTRIBUTE, SUPPORTED_ATTRIBUTE_NAMES,
};

use proc_macro2::{Span, TokenStream};

use quote::quote;

use syn::{
	fold::{self, Fold},
	parse::{Error, Parse, ParseStream, Result},
	parse_macro_input, parse_quote,
	spanned::Spanned,
	visit::{self, Visit},
	Attribute, FnArg, GenericParam, Generics, Ident, ItemTrait, Lit, Meta, NestedMeta, TraitBound,
	TraitItem, TraitItemMethod,
};

use std::collections::{BTreeMap, HashMap};

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

	generics.lt_token = Some(Default::default());
	generics.params.insert(0, parse_quote!( Block: #c::BlockT ));
	generics.gt_token = Some(Default::default());
}

/// Remove all attributes from the vector that are supported by us in the declaration of a runtime
/// api trait. The returned hashmap contains all found attribute names as keys and the rest of the
/// attribute body as `TokenStream`.
fn remove_supported_attributes(attrs: &mut Vec<Attribute>) -> HashMap<&'static str, Attribute> {
	let mut result = HashMap::new();
	attrs.retain(|v| match SUPPORTED_ATTRIBUTE_NAMES.iter().find(|a| v.path.is_ident(a)) {
		Some(attribute) => {
			result.insert(*attribute, v.clone());
			false
		},
		None => true,
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

/// Versioned API traits are used to catch missing methods when implementing a specific version of a
/// versioned API. They contain all non-versioned methods (aka stable methods) from the main trait
/// and all versioned methods for the specific version. This means that there is one trait for each
/// version mentioned in the trait definition. For example:
/// ```ignore
/// // The trait version implicitly is 1
/// decl_runtime_apis!(
/// 	trait SomeApi {
/// 		fn method1(); 	// this is a 'stable method'
///
/// 		#[api_version(2)]
/// 		fn method2();
///
/// 		#[api_version(2)]
/// 		fn method3();
///
/// 		#[api_version(3)]
/// 		fn method4();
/// 	}
/// );
/// ```
/// This trait has got three different versions. The function below will generate the following
/// code:
/// ```
/// trait SomeApiV1 {
/// 	// in V1 only the stable methods are required. The rest has got default implementations.
/// 	fn method1();
/// }
///
/// trait SomeApiV2 {
/// 	// V2 contains all methods from V1 and V2. V3 not required so they are skipped.
/// 	fn method1();
/// 	fn method2();
/// 	fn method3();
/// }
///
/// trait SomeApiV3 {
/// 	// And V3 contains all methods from the trait.
/// 	fn method1();
/// 	fn method2();
/// 	fn method3();
/// 	fn method4();
/// }
/// ```
fn generate_versioned_api_traits(
	api: ItemTrait,
	methods: BTreeMap<u64, Vec<TraitItemMethod>>,
) -> Vec<ItemTrait> {
	let mut result = Vec::<ItemTrait>::new();
	for (version, _) in &methods {
		let mut versioned_trait = api.clone();
		versioned_trait.ident = versioned_trait_name(&versioned_trait.ident, *version);
		versioned_trait.items = Vec::new();
		// Add the methods from the current version and all previous one. Versions are sorted so
		// it's safe to stop early.
		for (_, m) in methods.iter().take_while(|(v, _)| v <= &version) {
			versioned_trait.items.extend(m.iter().cloned().map(|m| TraitItem::Method(m)));
		}

		result.push(versioned_trait);
	}

	result
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
		Meta::List(list) =>
			if list.nested.len() > 2 && list.nested.is_empty() {
				err
			} else {
				let mut itr = list.nested.iter();
				let old_name = match itr.next() {
					Some(NestedMeta::Lit(Lit::Str(i))) => i.value(),
					_ => return err,
				};

				let version = match itr.next() {
					Some(NestedMeta::Lit(Lit::Int(i))) => i.base10_parse()?,
					_ => return err,
				};

				Ok((old_name, version))
			},
		_ => err,
	}
}

/// Generate the declaration of the trait for the runtime.
fn generate_runtime_decls(decls: &[ItemTrait]) -> Result<TokenStream> {
	let mut result = Vec::new();

	for decl in decls {
		let mut decl = decl.clone();
		let decl_span = decl.span();
		extend_generics_with_block(&mut decl.generics);
		let mod_name = generate_runtime_mod_name_for_trait(&decl.ident);
		let found_attributes = remove_supported_attributes(&mut decl.attrs);
		let api_version =
			get_api_version(&found_attributes).map(|v| generate_runtime_api_version(v as u32))?;
		let id = generate_runtime_api_id(&decl.ident.to_string());

		let trait_api_version = get_api_version(&found_attributes)?;

		let mut methods_by_version: BTreeMap<u64, Vec<TraitItemMethod>> = BTreeMap::new();

		// Process the items in the declaration. The filter_map function below does a lot of stuff
		// because the method attributes are stripped at this point
		decl.items.iter_mut().for_each(|i| match i {
			TraitItem::Method(ref mut method) => {
				let method_attrs = remove_supported_attributes(&mut method.attrs);
				let mut method_version = trait_api_version;
				// validate the api version for the method (if any) and generate default
				// implementation for versioned methods
				if let Some(version_attribute) = method_attrs.get(API_VERSION_ATTRIBUTE) {
					method_version = match parse_runtime_api_version(version_attribute) {
						Ok(method_api_ver) if method_api_ver < trait_api_version => {
							let method_ver = method_api_ver.to_string();
							let trait_ver = trait_api_version.to_string();
							let mut err1 = Error::new(
								version_attribute.span(),
								format!(
										"Method version `{}` is older than (or equal to) trait version `{}`.\
										 Methods can't define versions older than the trait version.",
										method_ver,
										trait_ver,
									),
							);

							let err2 = match found_attributes.get(&API_VERSION_ATTRIBUTE) {
								Some(attr) => Error::new(attr.span(), "Trait version is set here."),
								None => Error::new(
									decl_span,
									"Trait version is not set so it is implicitly equal to 1.",
								),
							};
							err1.combine(err2);
							result.push(err1.to_compile_error());

							trait_api_version
						},
						Ok(method_api_ver) => method_api_ver,
						Err(e) => {
							result.push(e.to_compile_error());
							trait_api_version
						},
					};
				}

				// Any method with the `changed_in` attribute isn't required for the runtime
				// anymore.
				if !method_attrs.contains_key(CHANGED_IN_ATTRIBUTE) {
					// Make sure we replace all the wild card parameter names.
					replace_wild_card_parameter_names(&mut method.sig);

					// partition methods by api version
					methods_by_version.entry(method_version).or_default().push(method.clone());
				}
			},
			_ => (),
		});

		let versioned_api_traits = generate_versioned_api_traits(decl.clone(), methods_by_version);

		let main_api_ident = decl.ident.clone();
		let versioned_ident = &versioned_api_traits
			.first()
			.expect("There should always be at least one version.")
			.ident;

		result.push(quote!(
			#[doc(hidden)]
			#[allow(dead_code)]
			#[allow(deprecated)]
			pub mod #mod_name {
				use super::*;

				#( #versioned_api_traits )*

				pub use #versioned_ident as #main_api_ident;

				pub #api_version

				pub #id
			}
		));
	}

	Ok(quote!( #( #result )* ))
}

/// Modify the given runtime api declaration to be usable on the client side.
struct ToClientSideDecl<'a> {
	block_hash: &'a TokenStream,
	crate_: &'a TokenStream,
	found_attributes: &'a mut HashMap<&'static str, Attribute>,
	/// Any error that we found while converting this declaration.
	errors: &'a mut Vec<TokenStream>,
	trait_: &'a Ident,
}

impl<'a> ToClientSideDecl<'a> {
	/// Process the given [`ItemTrait`].
	fn process(mut self, decl: ItemTrait) -> ItemTrait {
		let mut decl = self.fold_item_trait(decl);

		let block_hash = self.block_hash;
		let crate_ = self.crate_;

		// Add the special method that will be implemented by the `impl_runtime_apis!` macro
		// to enable functions to call into the runtime.
		decl.items.push(parse_quote! {
			/// !!INTERNAL USE ONLY!!
			#[doc(hidden)]
			fn __runtime_api_internal_call_api_at(
				&self,
				at: #block_hash,
				context: #crate_::ExecutionContext,
				params: std::vec::Vec<u8>,
				fn_name: &dyn Fn(#crate_::RuntimeVersion) -> &'static str,
			) -> std::result::Result<std::vec::Vec<u8>, #crate_::ApiError>;
		});

		decl
	}
}

impl<'a> ToClientSideDecl<'a> {
	fn fold_item_trait_items(
		&mut self,
		items: Vec<TraitItem>,
		trait_generics_num: usize,
	) -> Vec<TraitItem> {
		let mut result = Vec::new();

		items.into_iter().for_each(|i| match i {
			TraitItem::Method(method) => {
				let (fn_decl, fn_decl_ctx) =
					self.fold_trait_item_method(method, trait_generics_num);
				result.push(fn_decl.into());
				result.push(fn_decl_ctx.into());
			},
			r => result.push(r),
		});

		result
	}

	fn fold_trait_item_method(
		&mut self,
		method: TraitItemMethod,
		trait_generics_num: usize,
	) -> (TraitItemMethod, TraitItemMethod) {
		let crate_ = self.crate_;
		let context = quote!( #crate_::ExecutionContext::OffchainCall(None) );
		let fn_decl = self.create_method_decl(method.clone(), context, trait_generics_num);
		let fn_decl_ctx = self.create_method_decl_with_context(method, trait_generics_num);

		(fn_decl, fn_decl_ctx)
	}

	fn create_method_decl_with_context(
		&mut self,
		method: TraitItemMethod,
		trait_generics_num: usize,
	) -> TraitItemMethod {
		let crate_ = self.crate_;
		let context_arg: syn::FnArg = parse_quote!( context: #crate_::ExecutionContext );
		let mut fn_decl_ctx = self.create_method_decl(method, quote!(context), trait_generics_num);
		fn_decl_ctx.sig.ident =
			Ident::new(&format!("{}_with_context", &fn_decl_ctx.sig.ident), Span::call_site());
		fn_decl_ctx.sig.inputs.insert(2, context_arg);

		fn_decl_ctx
	}

	/// Takes the method declared by the user and creates the declaration we require for the runtime
	/// api client side. This method will call by default the `method_runtime_api_impl` for doing
	/// the actual call into the runtime.
	fn create_method_decl(
		&mut self,
		mut method: TraitItemMethod,
		context: TokenStream,
		trait_generics_num: usize,
	) -> TraitItemMethod {
		let params = match extract_parameter_names_types_and_borrows(
			&method.sig,
			AllowSelfRefInParameters::No,
		) {
			Ok(res) => res.into_iter().map(|v| v.0).collect::<Vec<_>>(),
			Err(e) => {
				self.errors.push(e.to_compile_error());
				Vec::new()
			},
		};
		let ret_type = return_type_extract_type(&method.sig.output);

		fold_fn_decl_for_client_side(&mut method.sig, self.block_hash, self.crate_);

		let crate_ = self.crate_;

		let found_attributes = remove_supported_attributes(&mut method.attrs);

		// Parse the renamed attributes.
		let mut renames = Vec::new();
		for (_, a) in found_attributes.iter().filter(|a| a.0 == &RENAMED_ATTRIBUTE) {
			match parse_renamed_attribute(a) {
				Ok((old_name, version)) => {
					renames.push((version, prefix_function_with_trait(&self.trait_, &old_name)));
				},
				Err(e) => self.errors.push(e.to_compile_error()),
			}
		}

		renames.sort_by(|l, r| r.cmp(l));
		let (versions, old_names) = renames.into_iter().fold(
			(Vec::new(), Vec::new()),
			|(mut versions, mut old_names), (version, old_name)| {
				versions.push(version);
				old_names.push(old_name);
				(versions, old_names)
			},
		);

		// Generate the function name before we may rename it below to
		// `function_name_before_version_{}`.
		let function_name = prefix_function_with_trait(&self.trait_, &method.sig.ident);

		// If the method has a `changed_in` attribute, we need to alter the method name to
		// `method_before_version_VERSION`.
		match get_changed_in(&found_attributes) {
			Ok(Some(version)) => {
				// Make sure that the `changed_in` version is at least the current `api_version`.
				if get_api_version(self.found_attributes).ok() < Some(version) {
					self.errors.push(
						Error::new(
							method.span(),
							"`changed_in` version can not be greater than the `api_version`",
						)
						.to_compile_error(),
					);
				}

				let ident = Ident::new(
					&format!("{}_before_version_{}", method.sig.ident, version),
					method.sig.ident.span(),
				);
				method.sig.ident = ident;
				method.attrs.push(parse_quote!( #[deprecated] ));
			},
			Ok(None) => {},
			Err(e) => {
				self.errors.push(e.to_compile_error());
			},
		};

		// The module where the runtime relevant stuff is declared.
		let trait_name = &self.trait_;
		let runtime_mod = generate_runtime_mod_name_for_trait(trait_name);
		let underscores = (0..trait_generics_num).map(|_| quote!(_));

		// Generate the default implementation that calls the `method_runtime_api_impl` method.
		method.default = Some(parse_quote! {
			{
				let __runtime_api_impl_params_encoded__ =
					#crate_::Encode::encode(&( #( &#params ),* ));

				<Self as #trait_name<#( #underscores ),*>>::__runtime_api_internal_call_api_at(
					self,
					__runtime_api_at_param__,
					#context,
					__runtime_api_impl_params_encoded__,
					&|version| {
						#(
							// Check if we need to call the function by an old name.
							if version.apis.iter().any(|(s, v)| {
								s == &#runtime_mod::ID && *v < #versions
							}) {
								return #old_names
							}
						)*

						#function_name
					}
				)
				.and_then(|r|
					std::result::Result::map_err(
						<#ret_type as #crate_::Decode>::decode(&mut &r[..]),
						|err| #crate_::ApiError::FailedToDecodeReturnValue {
							function: #function_name,
							error: err,
						}
					)
				)
			}
		});

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
			input.supertraits = parse_quote!('static + Send);
		} else {
			// Add the `Core` runtime api as super trait.
			let crate_ = &self.crate_;
			input.supertraits.push(parse_quote!( #crate_::Core<#block_ident> ));
		}

		// The client side trait is only required when compiling with the feature `std` or `test`.
		input.attrs.push(parse_quote!( #[cfg(any(feature = "std", test))] ));
		input.items = self.fold_item_trait_items(input.items, input.generics.params.len());

		fold::fold_item_trait(self, input)
	}
}

/// Generates the identifier as const variable for the given `trait_name`
/// by hashing the `trait_name`.
fn generate_runtime_api_id(trait_name: &str) -> TokenStream {
	use blake2::digest::{consts::U8, Digest};

	let mut res = [0; 8];
	res.copy_from_slice(blake2::Blake2b::<U8>::digest(trait_name).as_slice());

	quote!( const ID: [u8; 8] = [ #( #res ),* ]; )
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

	let impl_generics = trait_.generics.type_params().map(|t| {
		let ident = &t.ident;
		let colon_token = &t.colon_token;
		let bounds = &t.bounds;

		quote! { #ident #colon_token #bounds }
	});

	let ty_generics = trait_.generics.type_params().map(|t| {
		let ident = &t.ident;
		quote! { #ident }
	});

	quote!(
		#[cfg(any(feature = "std", test))]
		impl < #( #impl_generics, )* > #crate_::RuntimeApiInfo
			for dyn #trait_name < #( #ty_generics, )* >
		{
			#id
			#version
		}
	)
}

/// Get changed in version from the user given attribute or `Ok(None)`, if no attribute was given.
fn get_changed_in(found_attributes: &HashMap<&'static str, Attribute>) -> Result<Option<u64>> {
	found_attributes
		.get(&CHANGED_IN_ATTRIBUTE)
		.map(|v| parse_runtime_api_version(v).map(Some))
		.unwrap_or(Ok(None))
}

/// Get the api version from the user given attribute or `Ok(1)`, if no attribute was given.
fn get_api_version(found_attributes: &HashMap<&'static str, Attribute>) -> Result<u64> {
	found_attributes
		.get(&API_VERSION_ATTRIBUTE)
		.map(parse_runtime_api_version)
		.unwrap_or(Ok(1))
}

/// Generate the declaration of the trait for the client side.
fn generate_client_side_decls(decls: &[ItemTrait]) -> Result<TokenStream> {
	let mut result = Vec::new();

	for decl in decls {
		let decl = decl.clone();

		let crate_ = generate_crate_access(HIDDEN_INCLUDES_ID);
		let block_hash = quote!( <Block as #crate_::BlockT>::Hash );
		let mut found_attributes = HashMap::new();
		let mut errors = Vec::new();
		let trait_ = decl.ident.clone();

		let decl = ToClientSideDecl {
			crate_: &crate_,
			block_hash: &block_hash,
			found_attributes: &mut found_attributes,
			errors: &mut errors,
			trait_: &trait_,
		}
		.process(decl);

		let api_version = get_api_version(&found_attributes);

		let runtime_info = api_version.map(|v| generate_runtime_info_impl(&decl, v))?;

		result.push(quote!( #decl #runtime_info #( #errors )* ));
	}

	Ok(quote!( #( #result )* ))
}

/// Checks that a trait declaration is in the format we expect.
struct CheckTraitDecl {
	errors: Vec<Error>,
}

impl CheckTraitDecl {
	/// Check the given trait.
	///
	/// All errors will be collected in `self.errors`.
	fn check(&mut self, trait_: &ItemTrait) {
		self.check_method_declarations(trait_.items.iter().filter_map(|i| match i {
			TraitItem::Method(method) => Some(method),
			_ => None,
		}));

		visit::visit_item_trait(self, trait_);
	}

	/// Check that the given method declarations are correct.
	///
	/// Any error is stored in `self.errors`.
	fn check_method_declarations<'a>(
		&mut self,
		methods: impl Iterator<Item = &'a TraitItemMethod>,
	) {
		let mut method_to_signature_changed = HashMap::<Ident, Vec<Option<u64>>>::new();

		methods.into_iter().for_each(|method| {
			let attributes = remove_supported_attributes(&mut method.attrs.clone());

			let changed_in = match get_changed_in(&attributes) {
				Ok(r) => r,
				Err(e) => {
					self.errors.push(e);
					return
				},
			};

			method_to_signature_changed
				.entry(method.sig.ident.clone())
				.or_default()
				.push(changed_in);

			if method.default.is_some() {
				self.errors.push(Error::new(
					method.default.span(),
					"A runtime API function cannot have a default implementation!",
				));
			}
		});

		method_to_signature_changed.into_iter().for_each(|(f, changed)| {
			// If `changed_in` is `None`, it means it is the current "default" method that calls
			// into the latest implementation.
			if changed.iter().filter(|c| c.is_none()).count() == 0 {
				self.errors.push(Error::new(
					f.span(),
					"There is no 'default' method with this name (without `changed_in` attribute).\n\
					 The 'default' method is used to call into the latest implementation.",
				));
			}
		});
	}
}

impl<'ast> Visit<'ast> for CheckTraitDecl {
	fn visit_fn_arg(&mut self, input: &'ast FnArg) {
		if let FnArg::Receiver(_) = input {
			self.errors.push(Error::new(input.span(), "`self` as argument not supported."))
		}

		visit::visit_fn_arg(self, input);
	}

	fn visit_generic_param(&mut self, input: &'ast GenericParam) {
		match input {
			GenericParam::Type(ty) if ty.ident == BLOCK_GENERIC_IDENT =>
				self.errors.push(Error::new(
					input.span(),
					"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro!",
				)),
			_ => {},
		}

		visit::visit_generic_param(self, input);
	}

	fn visit_trait_bound(&mut self, input: &'ast TraitBound) {
		if let Some(last_ident) = input.path.segments.last().map(|v| &v.ident) {
			if last_ident == "BlockT" || last_ident == BLOCK_GENERIC_IDENT {
				self.errors.push(Error::new(
					input.span(),
					"`Block: BlockT` generic parameter will be added automatically by the \
						`decl_runtime_apis!` macro! If you try to use a different trait than the \
						substrate `Block` trait, please rename it locally.",
				))
			}
		}

		visit::visit_trait_bound(self, input)
	}
}

/// Check that the trait declarations are in the format we expect.
fn check_trait_decls(decls: &[ItemTrait]) -> Result<()> {
	let mut checker = CheckTraitDecl { errors: Vec::new() };
	decls.iter().for_each(|decl| checker.check(decl));

	if let Some(err) = checker.errors.pop() {
		Err(checker.errors.into_iter().fold(err, |mut err, other| {
			err.combine(other);
			err
		}))
	} else {
		Ok(())
	}
}

/// The implementation of the `decl_runtime_apis!` macro.
pub fn decl_runtime_apis_impl(input: proc_macro::TokenStream) -> proc_macro::TokenStream {
	// Parse all trait declarations
	let RuntimeApiDecls { decls: api_decls } = parse_macro_input!(input as RuntimeApiDecls);

	decl_runtime_apis_impl_inner(&api_decls)
		.unwrap_or_else(|e| e.to_compile_error())
		.into()
}

fn decl_runtime_apis_impl_inner(api_decls: &[ItemTrait]) -> Result<TokenStream> {
	check_trait_decls(api_decls)?;

	let hidden_includes = generate_hidden_includes(HIDDEN_INCLUDES_ID);
	let runtime_decls = generate_runtime_decls(api_decls)?;
	let client_side_decls = generate_client_side_decls(api_decls)?;

	Ok(quote!(
		#hidden_includes

		#runtime_decls

		#client_side_decls
	))
}
