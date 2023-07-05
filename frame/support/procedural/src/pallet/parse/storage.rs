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

use super::helper;
use frame_support_procedural_tools::get_doc_literals;
use quote::ToTokens;
use std::collections::HashMap;
use syn::spanned::Spanned;

/// List of additional token to be used for parsing.
mod keyword {
	syn::custom_keyword!(Error);
	syn::custom_keyword!(pallet);
	syn::custom_keyword!(getter);
	syn::custom_keyword!(storage_prefix);
	syn::custom_keyword!(unbounded);
	syn::custom_keyword!(whitelist_storage);
	syn::custom_keyword!(OptionQuery);
	syn::custom_keyword!(ResultQuery);
	syn::custom_keyword!(ValueQuery);
}

/// Parse for one of the following:
/// * `#[pallet::getter(fn dummy)]`
/// * `#[pallet::storage_prefix = "CustomName"]`
/// * `#[pallet::unbounded]`
/// * `#[pallet::whitelist_storage]
pub enum PalletStorageAttr {
	Getter(syn::Ident, proc_macro2::Span),
	StorageName(syn::LitStr, proc_macro2::Span),
	Unbounded(proc_macro2::Span),
	WhitelistStorage(proc_macro2::Span),
}

impl PalletStorageAttr {
	fn attr_span(&self) -> proc_macro2::Span {
		match self {
			Self::Getter(_, span) |
			Self::StorageName(_, span) |
			Self::Unbounded(span) |
			Self::WhitelistStorage(span) => *span,
		}
	}
}

impl syn::parse::Parse for PalletStorageAttr {
	fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
		input.parse::<syn::Token![#]>()?;
		let attr_span = input.span();
		let content;
		syn::bracketed!(content in input);
		content.parse::<keyword::pallet>()?;
		content.parse::<syn::Token![::]>()?;

		let lookahead = content.lookahead1();
		if lookahead.peek(keyword::getter) {
			content.parse::<keyword::getter>()?;

			let generate_content;
			syn::parenthesized!(generate_content in content);
			generate_content.parse::<syn::Token![fn]>()?;
			Ok(Self::Getter(generate_content.parse::<syn::Ident>()?, attr_span))
		} else if lookahead.peek(keyword::storage_prefix) {
			content.parse::<keyword::storage_prefix>()?;
			content.parse::<syn::Token![=]>()?;

			let renamed_prefix = content.parse::<syn::LitStr>()?;
			// Ensure the renamed prefix is a proper Rust identifier
			syn::parse_str::<syn::Ident>(&renamed_prefix.value()).map_err(|_| {
				let msg = format!("`{}` is not a valid identifier", renamed_prefix.value());
				syn::Error::new(renamed_prefix.span(), msg)
			})?;

			Ok(Self::StorageName(renamed_prefix, attr_span))
		} else if lookahead.peek(keyword::unbounded) {
			content.parse::<keyword::unbounded>()?;

			Ok(Self::Unbounded(attr_span))
		} else if lookahead.peek(keyword::whitelist_storage) {
			content.parse::<keyword::whitelist_storage>()?;
			Ok(Self::WhitelistStorage(attr_span))
		} else {
			Err(lookahead.error())
		}
	}
}

struct PalletStorageAttrInfo {
	getter: Option<syn::Ident>,
	rename_as: Option<syn::LitStr>,
	unbounded: bool,
	whitelisted: bool,
}

impl PalletStorageAttrInfo {
	fn from_attrs(attrs: Vec<PalletStorageAttr>) -> syn::Result<Self> {
		let mut getter = None;
		let mut rename_as = None;
		let mut unbounded = false;
		let mut whitelisted = false;
		for attr in attrs {
			match attr {
				PalletStorageAttr::Getter(ident, ..) if getter.is_none() => getter = Some(ident),
				PalletStorageAttr::StorageName(name, ..) if rename_as.is_none() =>
					rename_as = Some(name),
				PalletStorageAttr::Unbounded(..) if !unbounded => unbounded = true,
				PalletStorageAttr::WhitelistStorage(..) if !whitelisted => whitelisted = true,
				attr =>
					return Err(syn::Error::new(
						attr.attr_span(),
						"Invalid attribute: Duplicate attribute",
					)),
			}
		}

		Ok(PalletStorageAttrInfo { getter, rename_as, unbounded, whitelisted })
	}
}

/// The value and key types used by storages. Needed to expand metadata.
pub enum Metadata {
	Value { value: syn::Type },
	Map { value: syn::Type, key: syn::Type },
	CountedMap { value: syn::Type, key: syn::Type },
	DoubleMap { value: syn::Type, key1: syn::Type, key2: syn::Type },
	NMap { keys: Vec<syn::Type>, keygen: syn::Type, value: syn::Type },
}

pub enum QueryKind {
	OptionQuery,
	ResultQuery(syn::Path, syn::Ident),
	ValueQuery,
}

/// Definition of a storage, storage is a storage type like
/// `type MyStorage = StorageValue<MyStorageP, u32>`
/// The keys and values types are parsed in order to get metadata
pub struct StorageDef {
	/// The index of error item in pallet module.
	pub index: usize,
	/// Visibility of the storage type.
	pub vis: syn::Visibility,
	/// The type ident, to generate the StoragePrefix for.
	pub ident: syn::Ident,
	/// The keys and value metadata of the storage.
	pub metadata: Metadata,
	/// The doc associated to the storage.
	pub docs: Vec<syn::Expr>,
	/// A set of usage of instance, must be check for consistency with config.
	pub instances: Vec<helper::InstanceUsage>,
	/// Optional getter to generate. If some then query_kind is ensured to be some as well.
	pub getter: Option<syn::Ident>,
	/// Optional expression that evaluates to a type that can be used as StoragePrefix instead of
	/// ident.
	pub rename_as: Option<syn::LitStr>,
	/// Whereas the querytype of the storage is OptionQuery, ResultQuery or ValueQuery.
	/// Note that this is best effort as it can't be determined when QueryKind is generic, and
	/// result can be false if user do some unexpected type alias.
	pub query_kind: Option<QueryKind>,
	/// Where clause of type definition.
	pub where_clause: Option<syn::WhereClause>,
	/// The span of the pallet::storage attribute.
	pub attr_span: proc_macro2::Span,
	/// The `cfg` attributes.
	pub cfg_attrs: Vec<syn::Attribute>,
	/// If generics are named (e.g. `StorageValue<Value = u32, ..>`) then this contains all the
	/// generics of the storage.
	/// If generics are not named, this is none.
	pub named_generics: Option<StorageGenerics>,
	/// If the value stored in this storage is unbounded.
	pub unbounded: bool,
	/// Whether or not reads to this storage key will be ignored by benchmarking
	pub whitelisted: bool,
	/// Whether or not a default hasher is allowed to replace `_`
	pub use_default_hasher: bool,
}

/// The parsed generic from the
#[derive(Clone)]
pub enum StorageGenerics {
	DoubleMap {
		hasher1: syn::Type,
		key1: syn::Type,
		hasher2: syn::Type,
		key2: syn::Type,
		value: syn::Type,
		query_kind: Option<syn::Type>,
		on_empty: Option<syn::Type>,
		max_values: Option<syn::Type>,
	},
	Map {
		hasher: syn::Type,
		key: syn::Type,
		value: syn::Type,
		query_kind: Option<syn::Type>,
		on_empty: Option<syn::Type>,
		max_values: Option<syn::Type>,
	},
	CountedMap {
		hasher: syn::Type,
		key: syn::Type,
		value: syn::Type,
		query_kind: Option<syn::Type>,
		on_empty: Option<syn::Type>,
		max_values: Option<syn::Type>,
	},
	Value {
		value: syn::Type,
		query_kind: Option<syn::Type>,
		on_empty: Option<syn::Type>,
	},
	NMap {
		keygen: syn::Type,
		value: syn::Type,
		query_kind: Option<syn::Type>,
		on_empty: Option<syn::Type>,
		max_values: Option<syn::Type>,
	},
}

impl StorageGenerics {
	/// Return the metadata from the defined generics
	fn metadata(&self) -> syn::Result<Metadata> {
		let res = match self.clone() {
			Self::DoubleMap { value, key1, key2, .. } => Metadata::DoubleMap { value, key1, key2 },
			Self::Map { value, key, .. } => Metadata::Map { value, key },
			Self::CountedMap { value, key, .. } => Metadata::CountedMap { value, key },
			Self::Value { value, .. } => Metadata::Value { value },
			Self::NMap { keygen, value, .. } =>
				Metadata::NMap { keys: collect_keys(&keygen)?, keygen, value },
		};

		Ok(res)
	}

	/// Return the query kind from the defined generics
	fn query_kind(&self) -> Option<syn::Type> {
		match &self {
			Self::DoubleMap { query_kind, .. } |
			Self::Map { query_kind, .. } |
			Self::CountedMap { query_kind, .. } |
			Self::Value { query_kind, .. } |
			Self::NMap { query_kind, .. } => query_kind.clone(),
		}
	}
}

enum StorageKind {
	Value,
	Map,
	CountedMap,
	DoubleMap,
	NMap,
}

/// Check the generics in the `map` contains the generics in `gen` may contains generics in
/// `optional_gen`, and doesn't contains any other.
fn check_generics(
	map: &HashMap<String, syn::AssocType>,
	mandatory_generics: &[&str],
	optional_generics: &[&str],
	storage_type_name: &str,
	args_span: proc_macro2::Span,
) -> syn::Result<()> {
	let mut errors = vec![];

	let expectation = {
		let mut e = format!(
			"`{}` expect generics {}and optional generics {}",
			storage_type_name,
			mandatory_generics
				.iter()
				.map(|name| format!("`{}`, ", name))
				.collect::<String>(),
			&optional_generics.iter().map(|name| format!("`{}`, ", name)).collect::<String>(),
		);
		e.pop();
		e.pop();
		e.push('.');
		e
	};

	for (gen_name, gen_binding) in map {
		if !mandatory_generics.contains(&gen_name.as_str()) &&
			!optional_generics.contains(&gen_name.as_str())
		{
			let msg = format!(
				"Invalid pallet::storage, Unexpected generic `{}` for `{}`. {}",
				gen_name, storage_type_name, expectation,
			);
			errors.push(syn::Error::new(gen_binding.span(), msg));
		}
	}

	for mandatory_generic in mandatory_generics {
		if !map.contains_key(&mandatory_generic.to_string()) {
			let msg = format!(
				"Invalid pallet::storage, cannot find `{}` generic, required for `{}`.",
				mandatory_generic, storage_type_name
			);
			errors.push(syn::Error::new(args_span, msg));
		}
	}

	let mut errors = errors.drain(..);
	if let Some(mut error) = errors.next() {
		for other_error in errors {
			error.combine(other_error);
		}
		Err(error)
	} else {
		Ok(())
	}
}

/// Returns `(named generics, metadata, query kind, use_default_hasher)`
fn process_named_generics(
	storage: &StorageKind,
	args_span: proc_macro2::Span,
	args: &[syn::AssocType],
	dev_mode: bool,
) -> syn::Result<(Option<StorageGenerics>, Metadata, Option<syn::Type>, bool)> {
	let mut parsed = HashMap::<String, syn::AssocType>::new();

	// Ensure no duplicate.
	for arg in args {
		if let Some(other) = parsed.get(&arg.ident.to_string()) {
			let msg = "Invalid pallet::storage, Duplicated named generic";
			let mut err = syn::Error::new(arg.ident.span(), msg);
			err.combine(syn::Error::new(other.ident.span(), msg));
			return Err(err)
		}
		parsed.insert(arg.ident.to_string(), arg.clone());
	}

	let mut map_mandatory_generics = vec!["Key", "Value"];
	let mut map_optional_generics = vec!["QueryKind", "OnEmpty", "MaxValues"];
	if dev_mode {
		map_optional_generics.push("Hasher");
	} else {
		map_mandatory_generics.push("Hasher");
	}

	let generics = match storage {
		StorageKind::Value => {
			check_generics(
				&parsed,
				&["Value"],
				&["QueryKind", "OnEmpty"],
				"StorageValue",
				args_span,
			)?;

			StorageGenerics::Value {
				value: parsed
					.remove("Value")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				query_kind: parsed.remove("QueryKind").map(|binding| binding.ty),
				on_empty: parsed.remove("OnEmpty").map(|binding| binding.ty),
			}
		},
		StorageKind::Map => {
			check_generics(
				&parsed,
				&map_mandatory_generics,
				&map_optional_generics,
				"StorageMap",
				args_span,
			)?;

			StorageGenerics::Map {
				hasher: parsed
					.remove("Hasher")
					.map(|binding| binding.ty)
					.unwrap_or(syn::parse_quote!(Blake2_128Concat)),
				key: parsed
					.remove("Key")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				value: parsed
					.remove("Value")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				query_kind: parsed.remove("QueryKind").map(|binding| binding.ty),
				on_empty: parsed.remove("OnEmpty").map(|binding| binding.ty),
				max_values: parsed.remove("MaxValues").map(|binding| binding.ty),
			}
		},
		StorageKind::CountedMap => {
			check_generics(
				&parsed,
				&map_mandatory_generics,
				&map_optional_generics,
				"CountedStorageMap",
				args_span,
			)?;

			StorageGenerics::CountedMap {
				hasher: parsed
					.remove("Hasher")
					.map(|binding| binding.ty)
					.unwrap_or(syn::Type::Verbatim(quote::quote! { Blake2_128Concat })),
				key: parsed
					.remove("Key")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				value: parsed
					.remove("Value")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				query_kind: parsed.remove("QueryKind").map(|binding| binding.ty),
				on_empty: parsed.remove("OnEmpty").map(|binding| binding.ty),
				max_values: parsed.remove("MaxValues").map(|binding| binding.ty),
			}
		},
		StorageKind::DoubleMap => {
			let mut double_map_mandatory_generics = vec!["Key1", "Key2", "Value"];
			if dev_mode {
				map_optional_generics.extend(["Hasher1", "Hasher2"]);
			} else {
				double_map_mandatory_generics.extend(["Hasher1", "Hasher2"]);
			}

			check_generics(
				&parsed,
				&double_map_mandatory_generics,
				&map_optional_generics,
				"StorageDoubleMap",
				args_span,
			)?;

			StorageGenerics::DoubleMap {
				hasher1: parsed
					.remove("Hasher1")
					.map(|binding| binding.ty)
					.unwrap_or(syn::parse_quote!(Blake2_128Concat)),
				key1: parsed
					.remove("Key1")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				hasher2: parsed
					.remove("Hasher2")
					.map(|binding| binding.ty)
					.unwrap_or(syn::parse_quote!(Blake2_128Concat)),
				key2: parsed
					.remove("Key2")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				value: parsed
					.remove("Value")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				query_kind: parsed.remove("QueryKind").map(|binding| binding.ty),
				on_empty: parsed.remove("OnEmpty").map(|binding| binding.ty),
				max_values: parsed.remove("MaxValues").map(|binding| binding.ty),
			}
		},
		StorageKind::NMap => {
			check_generics(
				&parsed,
				&["Key", "Value"],
				&["QueryKind", "OnEmpty", "MaxValues"],
				"StorageNMap",
				args_span,
			)?;

			StorageGenerics::NMap {
				keygen: parsed
					.remove("Key")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				value: parsed
					.remove("Value")
					.map(|binding| binding.ty)
					.expect("checked above as mandatory generic"),
				query_kind: parsed.remove("QueryKind").map(|binding| binding.ty),
				on_empty: parsed.remove("OnEmpty").map(|binding| binding.ty),
				max_values: parsed.remove("MaxValues").map(|binding| binding.ty),
			}
		},
	};

	let metadata = generics.metadata()?;
	let query_kind = generics.query_kind();

	Ok((Some(generics), metadata, query_kind, false))
}

/// Returns `(named generics, metadata, query kind, use_default_hasher)`
fn process_unnamed_generics(
	storage: &StorageKind,
	args_span: proc_macro2::Span,
	args: &[syn::Type],
	dev_mode: bool,
) -> syn::Result<(Option<StorageGenerics>, Metadata, Option<syn::Type>, bool)> {
	let retrieve_arg = |arg_pos| {
		args.get(arg_pos).cloned().ok_or_else(|| {
			let msg = format!(
				"Invalid pallet::storage, unexpected number of generic argument, \
						expect at least {} args, found {}.",
				arg_pos + 1,
				args.len(),
			);
			syn::Error::new(args_span, msg)
		})
	};

	let prefix_arg = retrieve_arg(0)?;
	syn::parse2::<syn::Token![_]>(prefix_arg.to_token_stream()).map_err(|e| {
		let msg = "Invalid pallet::storage, for unnamed generic arguments the type \
				first generic argument must be `_`, the argument is then replaced by macro.";
		let mut err = syn::Error::new(prefix_arg.span(), msg);
		err.combine(e);
		err
	})?;

	let use_default_hasher = |arg_pos| {
		let arg = retrieve_arg(arg_pos)?;
		if syn::parse2::<syn::Token![_]>(arg.to_token_stream()).is_ok() {
			if dev_mode {
				Ok(true)
			} else {
				let msg = "`_` can only be used in dev_mode. Please specify an appropriate hasher.";
				Err(syn::Error::new(arg.span(), msg))
			}
		} else {
			Ok(false)
		}
	};

	let res = match storage {
		StorageKind::Value =>
			(None, Metadata::Value { value: retrieve_arg(1)? }, retrieve_arg(2).ok(), false),
		StorageKind::Map => (
			None,
			Metadata::Map { key: retrieve_arg(2)?, value: retrieve_arg(3)? },
			retrieve_arg(4).ok(),
			use_default_hasher(1)?,
		),
		StorageKind::CountedMap => (
			None,
			Metadata::CountedMap { key: retrieve_arg(2)?, value: retrieve_arg(3)? },
			retrieve_arg(4).ok(),
			use_default_hasher(1)?,
		),
		StorageKind::DoubleMap => (
			None,
			Metadata::DoubleMap {
				key1: retrieve_arg(2)?,
				key2: retrieve_arg(4)?,
				value: retrieve_arg(5)?,
			},
			retrieve_arg(6).ok(),
			use_default_hasher(1)? && use_default_hasher(3)?,
		),
		StorageKind::NMap => {
			let keygen = retrieve_arg(1)?;
			let keys = collect_keys(&keygen)?;
			(
				None,
				Metadata::NMap { keys, keygen, value: retrieve_arg(2)? },
				retrieve_arg(3).ok(),
				false,
			)
		},
	};

	Ok(res)
}

/// Returns `(named generics, metadata, query kind, use_default_hasher)`
fn process_generics(
	segment: &syn::PathSegment,
	dev_mode: bool,
) -> syn::Result<(Option<StorageGenerics>, Metadata, Option<syn::Type>, bool)> {
	let storage_kind = match &*segment.ident.to_string() {
		"StorageValue" => StorageKind::Value,
		"StorageMap" => StorageKind::Map,
		"CountedStorageMap" => StorageKind::CountedMap,
		"StorageDoubleMap" => StorageKind::DoubleMap,
		"StorageNMap" => StorageKind::NMap,
		found => {
			let msg = format!(
				"Invalid pallet::storage, expected ident: `StorageValue` or \
				`StorageMap` or `CountedStorageMap` or `StorageDoubleMap` or `StorageNMap` \
				in order to expand metadata, found `{}`.",
				found,
			);
			return Err(syn::Error::new(segment.ident.span(), msg))
		},
	};

	let args_span = segment.arguments.span();

	let args = match &segment.arguments {
		syn::PathArguments::AngleBracketed(args) if !args.args.is_empty() => args,
		_ => {
			let msg = "Invalid pallet::storage, invalid number of generic generic arguments, \
				expect more that 0 generic arguments.";
			return Err(syn::Error::new(segment.span(), msg))
		},
	};

	if args.args.iter().all(|gen| matches!(gen, syn::GenericArgument::Type(_))) {
		let args = args
			.args
			.iter()
			.map(|gen| match gen {
				syn::GenericArgument::Type(gen) => gen.clone(),
				_ => unreachable!("It is asserted above that all generics are types"),
			})
			.collect::<Vec<_>>();
		process_unnamed_generics(&storage_kind, args_span, &args, dev_mode)
	} else if args.args.iter().all(|gen| matches!(gen, syn::GenericArgument::AssocType(_))) {
		let args = args
			.args
			.iter()
			.map(|gen| match gen {
				syn::GenericArgument::AssocType(gen) => gen.clone(),
				_ => unreachable!("It is asserted above that all generics are bindings"),
			})
			.collect::<Vec<_>>();
		process_named_generics(&storage_kind, args_span, &args, dev_mode)
	} else {
		let msg = "Invalid pallet::storage, invalid generic declaration for storage. Expect only \
			type generics or binding generics, e.g. `<Name1 = Gen1, Name2 = Gen2, ..>` or \
			`<Gen1, Gen2, ..>`.";
		Err(syn::Error::new(segment.span(), msg))
	}
}

/// Parse the 2nd type argument to `StorageNMap` and return its keys.
fn collect_keys(keygen: &syn::Type) -> syn::Result<Vec<syn::Type>> {
	if let syn::Type::Tuple(tup) = keygen {
		tup.elems.iter().map(extract_key).collect::<syn::Result<Vec<_>>>()
	} else {
		Ok(vec![extract_key(keygen)?])
	}
}

/// In `Key<H, K>`, extract K and return it.
fn extract_key(ty: &syn::Type) -> syn::Result<syn::Type> {
	let typ = if let syn::Type::Path(typ) = ty {
		typ
	} else {
		let msg = "Invalid pallet::storage, expected type path";
		return Err(syn::Error::new(ty.span(), msg))
	};

	let key_struct = typ.path.segments.last().ok_or_else(|| {
		let msg = "Invalid pallet::storage, expected type path with at least one segment";
		syn::Error::new(typ.path.span(), msg)
	})?;
	if key_struct.ident != "Key" && key_struct.ident != "NMapKey" {
		let msg = "Invalid pallet::storage, expected Key or NMapKey struct";
		return Err(syn::Error::new(key_struct.ident.span(), msg))
	}

	let ty_params = if let syn::PathArguments::AngleBracketed(args) = &key_struct.arguments {
		args
	} else {
		let msg = "Invalid pallet::storage, expected angle bracketed arguments";
		return Err(syn::Error::new(key_struct.arguments.span(), msg))
	};

	if ty_params.args.len() != 2 {
		let msg = format!(
			"Invalid pallet::storage, unexpected number of generic arguments \
			for Key struct, expected 2 args, found {}",
			ty_params.args.len()
		);
		return Err(syn::Error::new(ty_params.span(), msg))
	}

	let key = match &ty_params.args[1] {
		syn::GenericArgument::Type(key_ty) => key_ty.clone(),
		_ => {
			let msg = "Invalid pallet::storage, expected type";
			return Err(syn::Error::new(ty_params.args[1].span(), msg))
		},
	};

	Ok(key)
}

impl StorageDef {
	/// Return the storage prefix for this storage item
	pub fn prefix(&self) -> String {
		self.rename_as
			.as_ref()
			.map(syn::LitStr::value)
			.unwrap_or_else(|| self.ident.to_string())
	}

	/// Return either the span of the ident or the span of the literal in the
	/// #[storage_prefix] attribute
	pub fn prefix_span(&self) -> proc_macro2::Span {
		self.rename_as
			.as_ref()
			.map(syn::LitStr::span)
			.unwrap_or_else(|| self.ident.span())
	}

	pub fn try_from(
		attr_span: proc_macro2::Span,
		index: usize,
		item: &mut syn::Item,
		dev_mode: bool,
	) -> syn::Result<Self> {
		let item = if let syn::Item::Type(item) = item {
			item
		} else {
			return Err(syn::Error::new(item.span(), "Invalid pallet::storage, expect item type."))
		};

		let attrs: Vec<PalletStorageAttr> = helper::take_item_pallet_attrs(&mut item.attrs)?;
		let PalletStorageAttrInfo { getter, rename_as, mut unbounded, whitelisted } =
			PalletStorageAttrInfo::from_attrs(attrs)?;

		// set all storages to be unbounded if dev_mode is enabled
		unbounded |= dev_mode;
		let cfg_attrs = helper::get_item_cfg_attrs(&item.attrs);

		let instances = vec![helper::check_type_def_gen(&item.generics, item.ident.span())?];

		let where_clause = item.generics.where_clause.clone();
		let docs = get_doc_literals(&item.attrs);

		let typ = if let syn::Type::Path(typ) = &*item.ty {
			typ
		} else {
			let msg = "Invalid pallet::storage, expected type path";
			return Err(syn::Error::new(item.ty.span(), msg))
		};

		if typ.path.segments.len() != 1 {
			let msg = "Invalid pallet::storage, expected type path with one segment";
			return Err(syn::Error::new(item.ty.span(), msg))
		}

		let (named_generics, metadata, query_kind, use_default_hasher) =
			process_generics(&typ.path.segments[0], dev_mode)?;

		let query_kind = query_kind
			.map(|query_kind| {
				use syn::{
					AngleBracketedGenericArguments, GenericArgument, Path, PathArguments, Type,
					TypePath,
				};

				let result_query = match query_kind {
					Type::Path(path)
						if path
							.path
							.segments
							.last()
							.map_or(false, |s| s.ident == "OptionQuery") =>
						return Ok(Some(QueryKind::OptionQuery)),
					Type::Path(TypePath { path: Path { segments, .. }, .. })
						if segments.last().map_or(false, |s| s.ident == "ResultQuery") =>
						segments
							.last()
							.expect("segments is checked to have the last value; qed")
							.clone(),
					Type::Path(path)
						if path.path.segments.last().map_or(false, |s| s.ident == "ValueQuery") =>
						return Ok(Some(QueryKind::ValueQuery)),
					_ => return Ok(None),
				};

				let error_type = match result_query.arguments {
					PathArguments::AngleBracketed(AngleBracketedGenericArguments {
						args, ..
					}) => {
						if args.len() != 1 {
							let msg = format!(
								"Invalid pallet::storage, unexpected number of generic arguments \
								for ResultQuery, expected 1 type argument, found {}",
								args.len(),
							);
							return Err(syn::Error::new(args.span(), msg))
						}

						args[0].clone()
					},
					args => {
						let msg = format!(
							"Invalid pallet::storage, unexpected generic args for ResultQuery, \
							expected angle-bracketed arguments, found `{}`",
							args.to_token_stream().to_string()
						);
						return Err(syn::Error::new(args.span(), msg))
					},
				};

				match error_type {
					GenericArgument::Type(Type::Path(TypePath {
						path: Path { segments: err_variant, leading_colon },
						..
					})) => {
						if err_variant.len() < 2 {
							let msg = format!(
								"Invalid pallet::storage, unexpected number of path segments for \
								the generics in ResultQuery, expected a path with at least 2 \
								segments, found {}",
								err_variant.len(),
							);
							return Err(syn::Error::new(err_variant.span(), msg))
						}
						let mut error = err_variant.clone();
						let err_variant = error
							.pop()
							.expect("Checked to have at least 2; qed")
							.into_value()
							.ident;

						// Necessary here to eliminate the last double colon
						let last =
							error.pop().expect("Checked to have at least 2; qed").into_value();
						error.push_value(last);

						Ok(Some(QueryKind::ResultQuery(
							syn::Path { leading_colon, segments: error },
							err_variant,
						)))
					},
					gen_arg => {
						let msg = format!(
							"Invalid pallet::storage, unexpected generic argument kind, expected a \
							type path to a `PalletError` enum variant, found `{}`",
							gen_arg.to_token_stream().to_string(),
						);
						Err(syn::Error::new(gen_arg.span(), msg))
					},
				}
			})
			.transpose()?
			.unwrap_or(Some(QueryKind::OptionQuery));

		if let (None, Some(getter)) = (query_kind.as_ref(), getter.as_ref()) {
			let msg = "Invalid pallet::storage, cannot generate getter because QueryKind is not \
				identifiable. QueryKind must be `OptionQuery`, `ResultQuery`, `ValueQuery`, or default \
				one to be identifiable.";
			return Err(syn::Error::new(getter.span(), msg))
		}

		Ok(StorageDef {
			attr_span,
			index,
			vis: item.vis.clone(),
			ident: item.ident.clone(),
			instances,
			metadata,
			docs,
			getter,
			rename_as,
			query_kind,
			where_clause,
			cfg_attrs,
			named_generics,
			unbounded,
			whitelisted,
			use_default_hasher,
		})
	}
}
