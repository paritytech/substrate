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

//! Home of the parsing and expansion code for the new pallet benchmarking syntax

use derive_syn_parse::Parse;
use frame_support_procedural_tools::generate_crate_access_2018;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{quote, quote_spanned, ToTokens};
use syn::{
	parenthesized,
	parse::{Nothing, ParseStream},
	parse_quote,
	punctuated::Punctuated,
	spanned::Spanned,
	token::{Colon2, Comma, Gt, Lt, Paren},
	Attribute, Error, Expr, ExprBlock, ExprCall, ExprPath, FnArg, Item, ItemFn, ItemMod, LitInt,
	Pat, Path, PathArguments, PathSegment, Result, ReturnType, Signature, Stmt, Token, Type,
	TypePath, Visibility, WhereClause,
};

mod keywords {
	use syn::custom_keyword;

	custom_keyword!(benchmark);
	custom_keyword!(benchmarks);
	custom_keyword!(block);
	custom_keyword!(extra);
	custom_keyword!(extrinsic_call);
	custom_keyword!(skip_meta);
	custom_keyword!(BenchmarkError);
	custom_keyword!(Result);
}

/// This represents the raw parsed data for a param definition such as `x: Linear<10, 20>`.
#[derive(Clone)]
struct ParamDef {
	name: String,
	typ: Type,
	start: u32,
	end: u32,
}

/// Allows easy parsing of the `<10, 20>` component of `x: Linear<10, 20>`.
#[derive(Parse)]
struct RangeArgs {
	_lt_token: Lt,
	start: LitInt,
	_comma: Comma,
	end: LitInt,
	_gt_token: Gt,
}

#[derive(Clone, Debug)]
struct BenchmarkAttrs {
	skip_meta: bool,
	extra: bool,
}

/// Represents a single benchmark option
enum BenchmarkAttrKeyword {
	Extra,
	SkipMeta,
}

impl syn::parse::Parse for BenchmarkAttrKeyword {
	fn parse(input: ParseStream) -> Result<Self> {
		let lookahead = input.lookahead1();
		if lookahead.peek(keywords::extra) {
			let _extra: keywords::extra = input.parse()?;
			return Ok(BenchmarkAttrKeyword::Extra)
		} else if lookahead.peek(keywords::skip_meta) {
			let _skip_meta: keywords::skip_meta = input.parse()?;
			return Ok(BenchmarkAttrKeyword::SkipMeta)
		} else {
			return Err(lookahead.error())
		}
	}
}

impl syn::parse::Parse for BenchmarkAttrs {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		let lookahead = input.lookahead1();
		if !lookahead.peek(Paren) {
			let _nothing: Nothing = input.parse()?;
			return Ok(BenchmarkAttrs { skip_meta: false, extra: false })
		}
		let content;
		let _paren: Paren = parenthesized!(content in input);
		let mut extra = false;
		let mut skip_meta = false;
		let args = Punctuated::<BenchmarkAttrKeyword, Token![,]>::parse_terminated(&content)?;
		for arg in args.into_iter() {
			match arg {
				BenchmarkAttrKeyword::Extra => {
					if extra {
						return Err(content.error("`extra` can only be specified once"))
					}
					extra = true;
				},
				BenchmarkAttrKeyword::SkipMeta => {
					if skip_meta {
						return Err(content.error("`skip_meta` can only be specified once"))
					}
					skip_meta = true;
				},
			}
		}
		Ok(BenchmarkAttrs { extra, skip_meta })
	}
}

/// Represents the parsed extrinsic call for a benchmark
#[derive(Clone)]
enum BenchmarkCallDef {
	ExtrinsicCall { origin: Expr, expr_call: ExprCall, attr_span: Span }, // #[extrinsic_call]
	Block { block: ExprBlock, attr_span: Span },                          // #[block]
}

impl BenchmarkCallDef {
	/// Returns the `span()` for attribute
	fn attr_span(&self) -> Span {
		match self {
			BenchmarkCallDef::ExtrinsicCall { origin: _, expr_call: _, attr_span } => *attr_span,
			BenchmarkCallDef::Block { block: _, attr_span } => *attr_span,
		}
	}
}

/// Represents a parsed `#[benchmark]` or `#[instance_banchmark]` item.
#[derive(Clone)]
struct BenchmarkDef {
	params: Vec<ParamDef>,
	setup_stmts: Vec<Stmt>,
	call_def: BenchmarkCallDef,
	verify_stmts: Vec<Stmt>,
	last_stmt: Option<Stmt>,
	extra: bool,
	skip_meta: bool,
	fn_sig: Signature,
	fn_vis: Visibility,
	fn_attrs: Vec<Attribute>,
}

/// used to parse something compatible with `Result<T, E>`
#[derive(Parse)]
struct ResultDef {
	_result_kw: keywords::Result,
	_lt: Token![<],
	unit: Type,
	_comma: Comma,
	e_type: TypePath,
	_gt: Token![>],
}

/// Ensures that `ReturnType` is a `Result<(), BenchmarkError>`, if specified
fn ensure_valid_return_type(item_fn: &ItemFn) -> Result<()> {
	if let ReturnType::Type(_, typ) = &item_fn.sig.output {
		let non_unit = |span| return Err(Error::new(span, "expected `()`"));
		let Type::Path(TypePath { path, qself: _ }) = &**typ else {
				return Err(Error::new(
					typ.span(),
					"Only `Result<(), BenchmarkError>` or a blank return type is allowed on benchmark function definitions",
				))
			};
		let seg = path
			.segments
			.last()
			.expect("to be parsed as a TypePath, it must have at least one segment; qed");
		let res: ResultDef = syn::parse2(seg.to_token_stream())?;
		// ensure T in Result<T, E> is ()
		let Type::Tuple(tup) = res.unit else { return non_unit(res.unit.span()) };
		if !tup.elems.is_empty() {
			return non_unit(tup.span())
		}
		let TypePath { path, qself: _ } = res.e_type;
		let seg = path
			.segments
			.last()
			.expect("to be parsed as a TypePath, it must have at least one segment; qed");
		syn::parse2::<keywords::BenchmarkError>(seg.to_token_stream())?;
	}
	Ok(())
}

/// Parses params such as `x: Linear<0, 1>`
fn parse_params(item_fn: &ItemFn) -> Result<Vec<ParamDef>> {
	let mut params: Vec<ParamDef> = Vec::new();
	for arg in &item_fn.sig.inputs {
		let invalid_param = |span| {
			return Err(Error::new(
				span,
				"Invalid benchmark function param. A valid example would be `x: Linear<5, 10>`.",
			))
		};

		let FnArg::Typed(arg) = arg else { return invalid_param(arg.span()) };
		let Pat::Ident(ident) = &*arg.pat else { return invalid_param(arg.span()) };

		// check param name
		let var_span = ident.span();
		let invalid_param_name = || {
			return Err(Error::new(
					var_span,
					"Benchmark parameter names must consist of a single lowercase letter (a-z) and no other characters.",
				))
		};
		let name = ident.ident.to_token_stream().to_string();
		if name.len() > 1 {
			return invalid_param_name()
		};
		let Some(name_char) = name.chars().next() else { return invalid_param_name() };
		if !name_char.is_alphabetic() || !name_char.is_lowercase() {
			return invalid_param_name()
		}

		// parse type
		let typ = &*arg.ty;
		let Type::Path(tpath) = typ else { return invalid_param(typ.span()) };
		let Some(segment) = tpath.path.segments.last() else { return invalid_param(typ.span()) };
		let args = segment.arguments.to_token_stream().into();
		let Ok(args) = syn::parse::<RangeArgs>(args) else { return invalid_param(typ.span()) };
		let Ok(start) = args.start.base10_parse::<u32>() else { return invalid_param(args.start.span()) };
		let Ok(end) = args.end.base10_parse::<u32>() else { return invalid_param(args.end.span()) };

		if end < start {
			return Err(Error::new(
				args.start.span(),
				"The start of a `ParamRange` must be less than or equal to the end",
			))
		}

		params.push(ParamDef { name, typ: typ.clone(), start, end });
	}
	Ok(params)
}

/// Used in several places where the `#[extrinsic_call]` or `#[body]` annotation is missing
fn missing_call<T>(item_fn: &ItemFn) -> Result<T> {
	return Err(Error::new(
		item_fn.block.brace_token.span,
		"No valid #[extrinsic_call] or #[block] annotation could be found in benchmark function body."
	))
}

/// Finds the `BenchmarkCallDef` and its index (within the list of stmts for the fn) and
/// returns them. Also handles parsing errors for invalid / extra call defs. AKA this is
/// general handling for `#[extrinsic_call]` and `#[block]`
fn parse_call_def(item_fn: &ItemFn) -> Result<(usize, BenchmarkCallDef)> {
	// #[extrinsic_call] / #[block] handling
	let call_defs = item_fn.block.stmts.iter().enumerate().filter_map(|(i, child)| {
			if let Stmt::Semi(Expr::Call(expr_call), _semi) = child {
				// #[extrinsic_call] case
				expr_call.attrs.iter().enumerate().find_map(|(k, attr)| {
					let segment = attr.path.segments.last()?;
					let _: keywords::extrinsic_call = syn::parse(segment.ident.to_token_stream().into()).ok()?;
					let mut expr_call = expr_call.clone();

					// consume #[extrinsic_call] tokens
					expr_call.attrs.remove(k);

					// extract origin from expr_call
					let Some(origin) = expr_call.args.first().cloned() else {
						return Some(Err(Error::new(expr_call.span(), "Single-item extrinsic calls must specify their origin as the first argument.")))
					};

					Some(Ok((i, BenchmarkCallDef::ExtrinsicCall { origin, expr_call, attr_span: attr.span() })))
				})
			} else if let Stmt::Expr(Expr::Block(block)) = child {
				// #[block] case
				block.attrs.iter().enumerate().find_map(|(k, attr)| {
					let segment = attr.path.segments.last()?;
					let _: keywords::block = syn::parse(segment.ident.to_token_stream().into()).ok()?;
					let mut block = block.clone();

					// consume #[block] tokens
					block.attrs.remove(k);

					Some(Ok((i, BenchmarkCallDef::Block { block, attr_span: attr.span() })))
				})
			} else {
				None
			}
		}).collect::<Result<Vec<_>>>()?;
	Ok(match &call_defs[..] {
		[(i, call_def)] => (*i, call_def.clone()), // = 1
		[] => return missing_call(item_fn),
		_ =>
			return Err(Error::new(
				call_defs[1].1.attr_span(),
				"Only one #[extrinsic_call] or #[block] attribute is allowed per benchmark.",
			)),
	})
}

impl BenchmarkDef {
	/// Constructs a [`BenchmarkDef`] by traversing an existing [`ItemFn`] node.
	pub fn from(item_fn: &ItemFn, extra: bool, skip_meta: bool) -> Result<BenchmarkDef> {
		let params = parse_params(item_fn)?;
		ensure_valid_return_type(item_fn)?;
		let (i, call_def) = parse_call_def(&item_fn)?;

		let (verify_stmts, last_stmt) = match item_fn.sig.output {
			ReturnType::Default =>
			// no return type, last_stmt should be None
				(Vec::from(&item_fn.block.stmts[(i + 1)..item_fn.block.stmts.len()]), None),
			ReturnType::Type(_, _) => {
				// defined return type, last_stmt should be Result<(), BenchmarkError>
				// compatible and should not be included in verify_stmts
				if i + 1 >= item_fn.block.stmts.len() {
					return Err(Error::new(
						item_fn.block.span(),
						"Benchmark `#[block]` or `#[extrinsic_call]` item cannot be the \
						last statement of your benchmark function definition if you have \
						defined a return type. You should return something compatible \
						with Result<(), BenchmarkError> (i.e. `Ok(())`) as the last statement \
						or change your signature to a blank return type.",
					))
				}
				let Some(stmt) = item_fn.block.stmts.last() else { return missing_call(item_fn) };
				(
					Vec::from(&item_fn.block.stmts[(i + 1)..item_fn.block.stmts.len() - 1]),
					Some(stmt.clone()),
				)
			},
		};

		Ok(BenchmarkDef {
			params,
			setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
			call_def,
			verify_stmts,
			last_stmt,
			extra,
			skip_meta,
			fn_sig: item_fn.sig.clone(),
			fn_vis: item_fn.vis.clone(),
			fn_attrs: item_fn.attrs.clone(),
		})
	}
}

/// Parses and expands a `#[benchmarks]` or `#[instance_benchmarks]` invocation
pub fn benchmarks(
	attrs: TokenStream,
	tokens: TokenStream,
	instance: bool,
) -> syn::Result<TokenStream> {
	// gather module info
	let module: ItemMod = syn::parse(tokens)?;
	let mod_span = module.span();
	let where_clause = match syn::parse::<Nothing>(attrs.clone()) {
		Ok(_) => quote!(),
		Err(_) => syn::parse::<WhereClause>(attrs)?.predicates.to_token_stream(),
	};
	let mod_vis = module.vis;
	let mod_name = module.ident;

	// consume #[benchmarks] attribute by exclusing it from mod_attrs
	let mod_attrs: Vec<&Attribute> = module
		.attrs
		.iter()
		.filter(|attr| syn::parse2::<keywords::benchmarks>(attr.to_token_stream()).is_err())
		.collect();

	let mut benchmark_names: Vec<Ident> = Vec::new();
	let mut extra_benchmark_names: Vec<Ident> = Vec::new();
	let mut skip_meta_benchmark_names: Vec<Ident> = Vec::new();

	let (_brace, mut content) =
		module.content.ok_or(syn::Error::new(mod_span, "Module cannot be empty!"))?;

	// find all function defs marked with #[benchmark]
	let benchmark_fn_metas = content.iter_mut().filter_map(|stmt| {
		// parse as a function def first
		let Item::Fn(func) = stmt else { return None };

		// find #[benchmark] attribute on function def
		let benchmark_attr = func.attrs.iter().find_map(|attr| {
			let seg = attr.path.segments.last()?;
			syn::parse::<keywords::benchmark>(seg.ident.to_token_stream().into()).ok()?;
			Some(attr)
		})?;

		Some((benchmark_attr.clone(), func.clone(), stmt))
	});

	// parse individual benchmark defs and args
	for (benchmark_attr, func, stmt) in benchmark_fn_metas {
		// parse any args provided to #[benchmark]
		let attr_tokens = benchmark_attr.tokens.to_token_stream().into();
		let benchmark_args: BenchmarkAttrs = syn::parse(attr_tokens)?;

		// parse benchmark def
		let benchmark_def =
			BenchmarkDef::from(&func, benchmark_args.extra, benchmark_args.skip_meta)?;

		// record benchmark name
		let name = &func.sig.ident;
		benchmark_names.push(name.clone());

		// record name sets
		if benchmark_def.extra {
			extra_benchmark_names.push(name.clone());
		}
		if benchmark_def.skip_meta {
			skip_meta_benchmark_names.push(name.clone())
		}

		// expand benchmark
		let expanded = expand_benchmark(benchmark_def, name, instance, where_clause.clone());

		// replace original function def with expanded code
		*stmt = Item::Verbatim(expanded);
	}

	// generics
	let type_use_generics = match instance {
		false => quote!(T),
		true => quote!(T, I),
	};
	let type_impl_generics = match instance {
		false => quote!(T: Config),
		true => quote!(T: Config<I>, I: 'static),
	};

	let krate = generate_crate_access_2018("frame-benchmarking")?;
	let support = quote!(#krate::frame_support);

	// benchmark name variables
	let benchmark_names_str: Vec<String> = benchmark_names.iter().map(|n| n.to_string()).collect();
	let extra_benchmark_names_str: Vec<String> =
		extra_benchmark_names.iter().map(|n| n.to_string()).collect();
	let skip_meta_benchmark_names_str: Vec<String> =
		skip_meta_benchmark_names.iter().map(|n| n.to_string()).collect();
	let mut selected_benchmark_mappings: Vec<TokenStream2> = Vec::new();
	let mut benchmarks_by_name_mappings: Vec<TokenStream2> = Vec::new();
	let test_idents: Vec<Ident> = benchmark_names_str
		.iter()
		.map(|n| Ident::new(format!("test_{}", n).as_str(), Span::call_site()))
		.collect();
	for i in 0..benchmark_names.len() {
		let name_ident = &benchmark_names[i];
		let name_str = &benchmark_names_str[i];
		let test_ident = &test_idents[i];
		selected_benchmark_mappings.push(quote!(#name_str => SelectedBenchmark::#name_ident));
		benchmarks_by_name_mappings.push(quote!(#name_str => Self::#test_ident()))
	}

	// emit final quoted tokens
	let res = quote! {
		#(#mod_attrs)
		*
		#mod_vis mod #mod_name {
			#(#content)
			*

			#[allow(non_camel_case_types)]
			enum SelectedBenchmark {
				#(#benchmark_names),
				*
			}

			impl<#type_impl_generics> #krate::BenchmarkingSetup<#type_use_generics> for SelectedBenchmark where #where_clause {
				fn components(&self) -> #krate::Vec<(#krate::BenchmarkParameter, u32, u32)> {
					match self {
						#(
							Self::#benchmark_names => {
								<#benchmark_names as #krate::BenchmarkingSetup<#type_use_generics>>::components(&#benchmark_names)
							}
						)
						*
					}
				}

				fn instance(
					&self,
					components: &[(#krate::BenchmarkParameter, u32)],
					verify: bool,
				) -> Result<
					#krate::Box<dyn FnOnce() -> Result<(), #krate::BenchmarkError>>,
					#krate::BenchmarkError,
				> {
					match self {
						#(
							Self::#benchmark_names => {
								<#benchmark_names as #krate::BenchmarkingSetup<
									#type_use_generics
								>>::instance(&#benchmark_names, components, verify)
							}
						)
						*
					}
				}
			}
			#[cfg(any(feature = "runtime-benchmarks", test))]
			impl<#type_impl_generics> #krate::Benchmarking for Pallet<#type_use_generics>
			where T: frame_system::Config, #where_clause
			{
				fn benchmarks(
					extra: bool,
				) -> #krate::Vec<#krate::BenchmarkMetadata> {
					let mut all_names = #krate::vec![
						#(#benchmark_names_str),
						*
					];
					if !extra {
						let extra = [
							#(#extra_benchmark_names_str),
							*
						];
						all_names.retain(|x| !extra.contains(x));
					}
					all_names.into_iter().map(|benchmark| {
						let selected_benchmark = match benchmark {
							#(#selected_benchmark_mappings),
							*,
							_ => panic!("all benchmarks should be selectable")
						};
						let components = <SelectedBenchmark as #krate::BenchmarkingSetup<#type_use_generics>>::components(&selected_benchmark);
						#krate::BenchmarkMetadata {
							name: benchmark.as_bytes().to_vec(),
							components,
							// TODO: Not supported by V2 syntax as of yet.
							// https://github.com/paritytech/substrate/issues/13132
							pov_modes: vec![],
						}
					}).collect::<#krate::Vec<_>>()
				}

				fn run_benchmark(
					extrinsic: &[u8],
					c: &[(#krate::BenchmarkParameter, u32)],
					whitelist: &[#krate::TrackedStorageKey],
					verify: bool,
					internal_repeats: u32,
				) -> Result<#krate::Vec<#krate::BenchmarkResult>, #krate::BenchmarkError> {
					let extrinsic = #krate::str::from_utf8(extrinsic).map_err(|_| "`extrinsic` is not a valid utf-8 string!")?;
					let selected_benchmark = match extrinsic {
						#(#selected_benchmark_mappings),
						*,
						_ => return Err("Could not find extrinsic.".into()),
					};
					let mut whitelist = whitelist.to_vec();
					let whitelisted_caller_key = <frame_system::Account<
						T,
					> as #support::storage::StorageMap<_, _,>>::hashed_key_for(
						#krate::whitelisted_caller::<T::AccountId>()
					);
					whitelist.push(whitelisted_caller_key.into());
					let transactional_layer_key = #krate::TrackedStorageKey::new(
						#support::storage::transactional::TRANSACTION_LEVEL_KEY.into(),
					);
					whitelist.push(transactional_layer_key);
					// Whitelist the `:extrinsic_index`.
					let extrinsic_index = #krate::TrackedStorageKey::new(
						#krate::well_known_keys::EXTRINSIC_INDEX.into()
					);
					whitelist.push(extrinsic_index);
					#krate::benchmarking::set_whitelist(whitelist.clone());
					let mut results: #krate::Vec<#krate::BenchmarkResult> = #krate::Vec::new();

					// Always do at least one internal repeat...
					for _ in 0 .. internal_repeats.max(1) {
						// Always reset the state after the benchmark.
						#krate::defer!(#krate::benchmarking::wipe_db());

						// Set up the externalities environment for the setup we want to
						// benchmark.
						let closure_to_benchmark = <
							SelectedBenchmark as #krate::BenchmarkingSetup<#type_use_generics>
						>::instance(&selected_benchmark, c, verify)?;

						// Set the block number to at least 1 so events are deposited.
						if #krate::Zero::is_zero(&frame_system::Pallet::<T>::block_number()) {
							frame_system::Pallet::<T>::set_block_number(1u32.into());
						}

						// Commit the externalities to the database, flushing the DB cache.
						// This will enable worst case scenario for reading from the database.
						#krate::benchmarking::commit_db();

						// Access all whitelisted keys to get them into the proof recorder since the
						// recorder does now have a whitelist.
						for key in &whitelist {
							#krate::frame_support::storage::unhashed::get_raw(&key.key);
						}

						// Reset the read/write counter so we don't count operations in the setup process.
						#krate::benchmarking::reset_read_write_count();

						// Time the extrinsic logic.
						#krate::log::trace!(
							target: "benchmark",
							"Start Benchmark: {} ({:?})",
							extrinsic,
							c
						);

						let start_pov = #krate::benchmarking::proof_size();
						let start_extrinsic = #krate::benchmarking::current_time();

						closure_to_benchmark()?;

						let finish_extrinsic = #krate::benchmarking::current_time();
						let end_pov = #krate::benchmarking::proof_size();

						// Calculate the diff caused by the benchmark.
						let elapsed_extrinsic = finish_extrinsic.saturating_sub(start_extrinsic);
						let diff_pov = match (start_pov, end_pov) {
							(Some(start), Some(end)) => end.saturating_sub(start),
							_ => Default::default(),
						};

						// Commit the changes to get proper write count
						#krate::benchmarking::commit_db();
						#krate::log::trace!(
							target: "benchmark",
							"End Benchmark: {} ns", elapsed_extrinsic
						);
						let read_write_count = #krate::benchmarking::read_write_count();
						#krate::log::trace!(
							target: "benchmark",
							"Read/Write Count {:?}", read_write_count
						);

						// Time the storage root recalculation.
						let start_storage_root = #krate::benchmarking::current_time();
						#krate::storage_root(#krate::StateVersion::V1);
						let finish_storage_root = #krate::benchmarking::current_time();
						let elapsed_storage_root = finish_storage_root - start_storage_root;

						let skip_meta = [ #(#skip_meta_benchmark_names_str),* ];
						let read_and_written_keys = if skip_meta.contains(&extrinsic) {
							#krate::vec![(b"Skipped Metadata".to_vec(), 0, 0, false)]
						} else {
							#krate::benchmarking::get_read_and_written_keys()
						};

						results.push(#krate::BenchmarkResult {
							components: c.to_vec(),
							extrinsic_time: elapsed_extrinsic,
							storage_root_time: elapsed_storage_root,
							reads: read_write_count.0,
							repeat_reads: read_write_count.1,
							writes: read_write_count.2,
							repeat_writes: read_write_count.3,
							proof_size: diff_pov,
							keys: read_and_written_keys,
						});
					}

					return Ok(results);
				}
			}

			#[cfg(test)]
			impl<#type_impl_generics> Pallet<#type_use_generics> where T: ::frame_system::Config, #where_clause {
				/// Test a particular benchmark by name.
				///
				/// This isn't called `test_benchmark_by_name` just in case some end-user eventually
				/// writes a benchmark, itself called `by_name`; the function would be shadowed in
				/// that case.
				///
				/// This is generally intended to be used by child test modules such as those created
				/// by the `impl_benchmark_test_suite` macro. However, it is not an error if a pallet
				/// author chooses not to implement benchmarks.
				#[allow(unused)]
				fn test_bench_by_name(name: &[u8]) -> Result<(), #krate::BenchmarkError> {
					let name = #krate::str::from_utf8(name)
						.map_err(|_| -> #krate::BenchmarkError { "`name` is not a valid utf8 string!".into() })?;
					match name {
						#(#benchmarks_by_name_mappings),
						*,
						_ => Err("Could not find test for requested benchmark.".into()),
					}
				}
			}
		}
		#mod_vis use #mod_name::*;
	};
	Ok(res.into())
}

/// Prepares a [`Vec<ParamDef>`] to be interpolated by [`quote!`] by creating easily-iterable
/// arrays formatted in such a way that they can be interpolated directly.
struct UnrolledParams {
	param_ranges: Vec<TokenStream2>,
	param_names: Vec<TokenStream2>,
	param_types: Vec<TokenStream2>,
}

impl UnrolledParams {
	/// Constructs an [`UnrolledParams`] from a [`Vec<ParamDef>`]
	fn from(params: &Vec<ParamDef>) -> UnrolledParams {
		let param_ranges: Vec<TokenStream2> = params
			.iter()
			.map(|p| {
				let name = Ident::new(&p.name, Span::call_site());
				let start = p.start;
				let end = p.end;
				quote!(#name, #start, #end)
			})
			.collect();
		let param_names: Vec<TokenStream2> = params
			.iter()
			.map(|p| {
				let name = Ident::new(&p.name, Span::call_site());
				quote!(#name)
			})
			.collect();
		let param_types: Vec<TokenStream2> = params
			.iter()
			.map(|p| {
				let typ = &p.typ;
				quote!(#typ)
			})
			.collect();
		UnrolledParams { param_ranges, param_names, param_types }
	}
}

/// Performs expansion of an already-parsed [`BenchmarkDef`].
fn expand_benchmark(
	benchmark_def: BenchmarkDef,
	name: &Ident,
	is_instance: bool,
	where_clause: TokenStream2,
) -> TokenStream2 {
	// set up variables needed during quoting
	let krate = match generate_crate_access_2018("frame-benchmarking") {
		Ok(ident) => ident,
		Err(err) => return err.to_compile_error().into(),
	};
	let home = quote!(#krate::v2);
	let codec = quote!(#krate::frame_support::codec);
	let traits = quote!(#krate::frame_support::traits);
	let setup_stmts = benchmark_def.setup_stmts;
	let verify_stmts = benchmark_def.verify_stmts;
	let last_stmt = benchmark_def.last_stmt;
	let test_ident = Ident::new(format!("test_{}", name.to_string()).as_str(), Span::call_site());

	// unroll params (prepare for quoting)
	let unrolled = UnrolledParams::from(&benchmark_def.params);
	let param_names = unrolled.param_names;
	let param_ranges = unrolled.param_ranges;
	let param_types = unrolled.param_types;

	let type_use_generics = match is_instance {
		false => quote!(T),
		true => quote!(T, I),
	};

	let type_impl_generics = match is_instance {
		false => quote!(T: Config),
		true => quote!(T: Config<I>, I: 'static),
	};

	// used in the benchmarking impls
	let (pre_call, post_call, fn_call_body) = match &benchmark_def.call_def {
		BenchmarkCallDef::ExtrinsicCall { origin, expr_call, attr_span: _ } => {
			let mut expr_call = expr_call.clone();

			// remove first arg from expr_call
			let mut final_args = Punctuated::<Expr, Comma>::new();
			let args: Vec<&Expr> = expr_call.args.iter().collect();
			for arg in &args[1..] {
				final_args.push((*(*arg)).clone());
			}
			expr_call.args = final_args;

			// determine call name (handles `_` and normal call syntax)
			let expr_span = expr_call.span();
			let call_err = || {
				quote_spanned!(expr_span=> "Extrinsic call must be a function call or `_`".to_compile_error()).into()
			};
			let call_name = match *expr_call.func {
				Expr::Path(expr_path) => {
					// normal function call
					let Some(segment) = expr_path.path.segments.last() else { return call_err(); };
					segment.ident.to_string()
				},
				Expr::Verbatim(tokens) => {
					// `_` style
					// replace `_` with fn name
					let Ok(_) = syn::parse::<Token![_]>(tokens.to_token_stream().into()) else { return call_err(); };
					name.to_string()
				},
				_ => return call_err(),
			};

			// modify extrinsic call to be prefixed with "new_call_variant"
			let call_name = format!("new_call_variant_{}", call_name);
			let mut punct: Punctuated<PathSegment, Colon2> = Punctuated::new();
			punct.push(PathSegment {
				arguments: PathArguments::None,
				ident: Ident::new(call_name.as_str(), Span::call_site()),
			});
			*expr_call.func = Expr::Path(ExprPath {
				attrs: vec![],
				qself: None,
				path: Path { leading_colon: None, segments: punct },
			});
			let pre_call = quote! {
				let __call = Call::<#type_use_generics>::#expr_call;
				let __benchmarked_call_encoded = #codec::Encode::encode(&__call);
			};
			let post_call = quote! {
				let __call_decoded = <Call<#type_use_generics> as #codec::Decode>
					::decode(&mut &__benchmarked_call_encoded[..])
					.expect("call is encoded above, encoding must be correct");
				let __origin = #origin.into();
				<Call<#type_use_generics> as #traits::UnfilteredDispatchable>::dispatch_bypass_filter(
					__call_decoded,
					__origin,
				)
			};
			(
				// (pre_call, post_call, fn_call_body):
				pre_call.clone(),
				quote!(#post_call?;),
				quote! {
					#pre_call
					#post_call.unwrap();
				},
			)
		},
		BenchmarkCallDef::Block { block, attr_span: _ } =>
			(quote!(), quote!(#block), quote!(#block)),
	};

	let vis = benchmark_def.fn_vis;

	// remove #[benchmark] attribute
	let fn_attrs: Vec<&Attribute> = benchmark_def
		.fn_attrs
		.iter()
		.filter(|attr| !syn::parse2::<keywords::benchmark>(attr.path.to_token_stream()).is_ok())
		.collect();

	// modify signature generics, ident, and inputs, e.g:
	// before: `fn bench(u: Linear<1, 100>) -> Result<(), BenchmarkError>`
	// after: `fn _bench <T: Config<I>, I: 'static>(u: u32, verify: bool) -> Result<(),
	// BenchmarkError>`
	let mut sig = benchmark_def.fn_sig;
	sig.generics = parse_quote!(<#type_impl_generics>);
	if !where_clause.is_empty() {
		sig.generics.where_clause = parse_quote!(where #where_clause);
	}
	sig.ident =
		Ident::new(format!("_{}", name.to_token_stream().to_string()).as_str(), Span::call_site());
	let mut fn_param_inputs: Vec<TokenStream2> =
		param_names.iter().map(|name| quote!(#name: u32)).collect();
	fn_param_inputs.push(quote!(verify: bool));
	sig.inputs = parse_quote!(#(#fn_param_inputs),*);

	// used in instance() impl
	let impl_last_stmt = match &last_stmt {
		Some(stmt) => quote!(#stmt),
		None => quote!(Ok(())),
	};

	let fn_def = quote! {
		#(
			#fn_attrs
		)*
		#vis #sig {
			#(
				#setup_stmts
			)*
			#fn_call_body
			if verify {
				#(
					#verify_stmts
				)*
			}
			#last_stmt
		}
	};

	// generate final quoted tokens
	let res = quote! {
		// benchmark function definition
		#fn_def

		// compile-time assertions that each referenced param type implements ParamRange
		#(
			#home::assert_impl_all!(#param_types: #home::ParamRange);
		)*

		#[allow(non_camel_case_types)]
		#(
			#fn_attrs
		)*
		struct #name;

		#[allow(unused_variables)]
		impl<#type_impl_generics> #krate::BenchmarkingSetup<#type_use_generics>
		for #name where #where_clause {
			fn components(&self) -> #krate::Vec<(#krate::BenchmarkParameter, u32, u32)> {
				#krate::vec! [
					#(
						(#krate::BenchmarkParameter::#param_ranges)
					),*
				]
			}

			fn instance(
				&self,
				components: &[(#krate::BenchmarkParameter, u32)],
				verify: bool
			) -> Result<#krate::Box<dyn FnOnce() -> Result<(), #krate::BenchmarkError>>, #krate::BenchmarkError> {
				#(
					// prepare instance #param_names
					let #param_names = components.iter()
						.find(|&c| c.0 == #krate::BenchmarkParameter::#param_names)
						.ok_or("Could not find component during benchmark preparation.")?
						.1;
				)*

				// benchmark setup code
				#(
					#setup_stmts
				)*
				#pre_call
				Ok(#krate::Box::new(move || -> Result<(), #krate::BenchmarkError> {
					#post_call
					if verify {
						#(
							#verify_stmts
						)*
					}
					#impl_last_stmt
				}))
			}
		}

		#[cfg(test)]
		impl<#type_impl_generics> Pallet<#type_use_generics> where T: ::frame_system::Config, #where_clause {
			#[allow(unused)]
			fn #test_ident() -> Result<(), #krate::BenchmarkError> {
				let selected_benchmark = SelectedBenchmark::#name;
				let components = <
					SelectedBenchmark as #krate::BenchmarkingSetup<T, _>
				>::components(&selected_benchmark);
				let execute_benchmark = |
					c: #krate::Vec<(#krate::BenchmarkParameter, u32)>
				| -> Result<(), #krate::BenchmarkError> {
					// Always reset the state after the benchmark.
					#krate::defer!(#krate::benchmarking::wipe_db());

					// Set up the benchmark, return execution + verification function.
					let closure_to_verify = <
						SelectedBenchmark as #krate::BenchmarkingSetup<T, _>
					>::instance(&selected_benchmark, &c, true)?;

					// Set the block number to at least 1 so events are deposited.
					if #krate::Zero::is_zero(&frame_system::Pallet::<T>::block_number()) {
						frame_system::Pallet::<T>::set_block_number(1u32.into());
					}

					// Run execution + verification
					closure_to_verify()
				};

				if components.is_empty() {
					execute_benchmark(Default::default())?;
				} else {
					let num_values: u32 = if let Ok(ev) = std::env::var("VALUES_PER_COMPONENT") {
						ev.parse().map_err(|_| {
							#krate::BenchmarkError::Stop(
								"Could not parse env var `VALUES_PER_COMPONENT` as u32."
							)
						})?
					} else {
						6
					};

					if num_values < 2 {
						return Err("`VALUES_PER_COMPONENT` must be at least 2".into());
					}

					for (name, low, high) in components.clone().into_iter() {
						// Test the lowest, highest (if its different from the lowest)
						// and up to num_values-2 more equidistant values in between.
						// For 0..10 and num_values=6 this would mean: [0, 2, 4, 6, 8, 10]

						let mut values = #krate::vec![low];
						let diff = (high - low).min(num_values - 1);
						let slope = (high - low) as f32 / diff as f32;

						for i in 1..=diff {
							let value = ((low as f32 + slope * i as f32) as u32)
											.clamp(low, high);
							values.push(value);
						}

						for component_value in values {
							// Select the max value for all the other components.
							let c: #krate::Vec<(#krate::BenchmarkParameter, u32)> = components
								.iter()
								.map(|(n, _, h)|
									if *n == name {
										(*n, component_value)
									} else {
										(*n, *h)
									}
								)
								.collect();

							execute_benchmark(c)?;
						}
					}
				}
				return Ok(());
			}
		}
	};
	res
}
