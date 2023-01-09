// This file is part of Substrate.

// Copyright (C) 2023 Parity Technologies (UK) Ltd.
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
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{
	parenthesized,
	parse::{Nothing, ParseStream},
	parse_macro_input,
	punctuated::Punctuated,
	spanned::Spanned,
	token::{Comma, Gt, Lt, Paren},
	Error, Expr, ExprBlock, ExprCall, FnArg, Item, ItemFn, ItemMod, LitInt, Pat, Result, Stmt,
	Token, Type, WhereClause,
};

mod keywords {
	use syn::custom_keyword;

	custom_keyword!(extrinsic_call);
	custom_keyword!(benchmark);
	custom_keyword!(extra);
	custom_keyword!(skip_meta);
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
enum ExtrinsicCallDef {
	Encoded { origin: Expr, expr_call: ExprCall }, // no block, just an extrinsic call
	Block(ExprBlock),                              // call is somewhere in the block
}

/// Represents a parsed `#[benchmark]` or `#[instance_banchmark]` item.
#[derive(Clone)]
struct BenchmarkDef {
	params: Vec<ParamDef>,
	setup_stmts: Vec<Stmt>,
	extrinsic_call: ExtrinsicCallDef,
	verify_stmts: Vec<Stmt>,
	extra: bool,
	skip_meta: bool,
}

impl BenchmarkDef {
	/// Constructs a [`BenchmarkDef`] by traversing an existing [`ItemFn`] node.
	pub fn from(item_fn: &ItemFn, extra: bool, skip_meta: bool) -> Result<BenchmarkDef> {
		let mut i = 0; // index of child
		let mut params: Vec<ParamDef> = Vec::new();

		// parse params such as "x: Linear<0, 1>"
		for arg in &item_fn.sig.inputs {
			let mut name: Option<String> = None;
			let mut typ: Option<&Type> = None;
			let mut start: Option<u32> = None;
			let mut end: Option<u32> = None;
			if let FnArg::Typed(arg) = arg {
				if let Pat::Ident(ident) = &*arg.pat {
					name = Some(ident.ident.to_token_stream().to_string());
				}
				let tmp = &*arg.ty;
				typ = Some(tmp);
				if let Type::Path(tpath) = tmp {
					if let Some(segment) = tpath.path.segments.last() {
						let args = segment.arguments.to_token_stream().into();
						if let Ok(args) = syn::parse::<RangeArgs>(args) {
							if let Ok(start_parsed) = args.start.base10_parse::<u32>() {
								start = Some(start_parsed);
							}
							if let Ok(end_parsed) = args.end.base10_parse::<u32>() {
								end = Some(end_parsed);
							}
						}
					}
				}
			}
			if let (Some(name), Some(typ), Some(start), Some(end)) = (name, typ, start, end) {
				// if true, this iteration of param extraction was successful
				params.push(ParamDef { name, typ: typ.clone(), start, end });
			} else {
				return Err(Error::new(
					arg.span(),
					"Invalid benchmark function param. A valid example would be `x: Linear<5, 10>`.",
				))
			}
		}

		// #[extrinsic_call] handling
		for child in &item_fn.block.stmts {
			let mut extrinsic_call: Option<ExtrinsicCallDef> = None;
			if let Stmt::Semi(Expr::Call(expr_call), _semi) = child {
				// non-block (encoded) case
				for (k, attr) in (&expr_call.attrs).iter().enumerate() {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							let mut expr_call = expr_call.clone();

							// consume #[extrinsic_call] tokens
							expr_call.attrs.remove(k);

							// extract origin from expr_call
							let origin = match expr_call.args.first() {
								Some(arg) => arg.clone(),
								None =>
									return Err(Error::new(
										expr_call.args.span(),
										"Single-item extrinsic calls must specify their origin as the first argument.",
									)),
							};
							extrinsic_call = Some(ExtrinsicCallDef::Encoded { origin, expr_call });
						}
					}
				}
			} else if let Stmt::Expr(Expr::Block(block)) = child {
				// block case
				for (k, attr) in (&block.attrs).iter().enumerate() {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							let mut block = block.clone();

							// consume #[extrinsic_call] tokens
							block.attrs.remove(k);

							extrinsic_call = Some(ExtrinsicCallDef::Block(block));
						}
					}
				}
			}

			// return parsed BenchmarkDef
			if let Some(extrinsic_call) = extrinsic_call {
				return Ok(BenchmarkDef {
					params,
					setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
					extrinsic_call,
					verify_stmts: Vec::from(
						&item_fn.block.stmts[(i + 1)..item_fn.block.stmts.len()],
					),
					extra,
					skip_meta,
				})
			}
			i += 1;
		}
		return Err(Error::new(
			item_fn.block.brace_token.span,
			"No valid #[extrinsic_call] annotation could be found in benchmark function body.",
		))
	}
}

/// Parses and expands a `#[benchmarks]` or `#[instance_benchmarks]` invocation
pub fn benchmarks(attrs: TokenStream, tokens: TokenStream, instance: bool) -> TokenStream {
	let module = parse_macro_input!(tokens as ItemMod);
	let where_clause = match syn::parse::<Nothing>(attrs.clone()) {
		Ok(_) => quote!(),
		Err(_) => parse_macro_input!(attrs as WhereClause).predicates.to_token_stream(),
	};
	let mod_vis = module.vis;
	let mod_name = module.ident;
	let mut expanded_stmts: Vec<TokenStream2> = Vec::new();
	let mut benchmark_defs: Vec<BenchmarkDef> = Vec::new();
	let mut benchmark_names: Vec<Ident> = Vec::new();
	let mut extra_benchmark_names: Vec<Ident> = Vec::new();
	let mut skip_meta_benchmark_names: Vec<Ident> = Vec::new();
	let mut args: Option<BenchmarkAttrs> = None;
	if let Some(mut content) = module.content {
		for stmt in &mut content.1 {
			let mut found_item: Option<ItemFn> = None;
			if let Item::Fn(func) = stmt {
				let mut i = 0;
				for attr in &func.attrs.clone() {
					if let Some(seg) = attr.path.segments.last() {
						if let Ok(_) =
							syn::parse::<keywords::benchmark>(seg.ident.to_token_stream().into())
						{
							let tokens = attr.tokens.to_token_stream().into();
							args = Some(parse_macro_input!(tokens as BenchmarkAttrs));
							func.attrs.remove(i);
							found_item = Some(func.clone());
							i += 1;
						}
					}
				}
			}
			if let (Some(item_fn), Some(args)) = (found_item, &args) {
				// this item is a #[benchmark] or #[instance_benchmark]
				let benchmark_def = match BenchmarkDef::from(&item_fn, args.extra, args.skip_meta) {
					Ok(def) => def,
					Err(err) => return err.to_compile_error().into(),
				};

				// expand benchmark
				let expanded = expand_benchmark(
					benchmark_def.clone(),
					&item_fn.sig.ident,
					instance,
					where_clause.clone(),
				);

				// record benchmark name
				let name = item_fn.sig.ident;
				benchmark_names.push(name.clone());
				if benchmark_def.extra {
					extra_benchmark_names.push(name.clone());
				}
				if benchmark_def.skip_meta {
					skip_meta_benchmark_names.push(name.clone())
				}

				expanded_stmts.push(expanded);
				benchmark_defs.push(benchmark_def);
			} else {
				// this is not a benchmark item, copy it in verbatim
				expanded_stmts.push(stmt.to_token_stream());
			}
		}
	}

	// generics
	let generics = match instance {
		false => quote!(T),
		true => quote!(T, I),
	};
	let full_generics = match instance {
		false => quote!(T: Config),
		true => quote!(T: Config<I>, I: 'static),
	};

	let krate = quote!(::frame_benchmarking);
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
		#mod_vis mod #mod_name {
			#(#expanded_stmts)
			*

			#[allow(non_camel_case_types)]
			enum SelectedBenchmark {
				#(#benchmark_names),
				*
			}

			impl<#full_generics> #krate::BenchmarkingSetup<#generics> for SelectedBenchmark where #where_clause {
				fn components(&self) -> #krate::Vec<(#krate::BenchmarkParameter, u32, u32)> {
					match self {
						#(
							Self::#benchmark_names => {
								<#benchmark_names as #krate::BenchmarkingSetup<#generics>>::components(&#benchmark_names)
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
									#generics
								>>::instance(&#benchmark_names, components, verify)
							}
						)
						*
					}
				}
			}
			#[cfg(any(feature = "runtime-benchmarks", test))]
			impl<#full_generics> #krate::Benchmarking for Pallet<#generics>
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
						let components = <SelectedBenchmark as #krate::BenchmarkingSetup<#generics>>::components(&selected_benchmark);
						#krate::BenchmarkMetadata {
							name: benchmark.as_bytes().to_vec(),
							components,
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
					#krate::benchmarking::set_whitelist(whitelist);
					let mut results: #krate::Vec<#krate::BenchmarkResult> = #krate::Vec::new();

					// Always do at least one internal repeat...
					for _ in 0 .. internal_repeats.max(1) {
						// Always reset the state after the benchmark.
						#krate::defer!(#krate::benchmarking::wipe_db());

						// Set up the externalities environment for the setup we want to
						// benchmark.
						let closure_to_benchmark = <
							SelectedBenchmark as #krate::BenchmarkingSetup<#generics>
						>::instance(&selected_benchmark, c, verify)?;

						// Set the block number to at least 1 so events are deposited.
						if #krate::Zero::is_zero(&frame_system::Pallet::<T>::block_number()) {
							frame_system::Pallet::<T>::set_block_number(1u32.into());
						}

						// Commit the externalities to the database, flushing the DB cache.
						// This will enable worst case scenario for reading from the database.
						#krate::benchmarking::commit_db();

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
			impl<#full_generics> Pallet<#generics> where T: ::frame_system::Config, #where_clause {
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
	res.into()
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
	let krate = quote!(::frame_benchmarking);
	let home = quote!(::frame_support::benchmarking);
	let codec = quote!(#krate::frame_support::codec);
	let traits = quote!(#krate::frame_support::traits);
	let setup_stmts = benchmark_def.setup_stmts;
	let verify_stmts = benchmark_def.verify_stmts;
	let test_ident = Ident::new(format!("test_{}", name.to_string()).as_str(), Span::call_site());

	// unroll params (prepare for quoting)
	let unrolled = UnrolledParams::from(&benchmark_def.params);
	let param_names = unrolled.param_names;
	let param_ranges = unrolled.param_ranges;
	let param_types = unrolled.param_types;

	let generics = match is_instance {
		false => quote!(T),
		true => quote!(T, I),
	};

	let full_generics = match is_instance {
		false => quote!(T: Config),
		true => quote!(T: Config<I>, I: 'static),
	};

	let (pre_call, post_call) = match benchmark_def.extrinsic_call {
		ExtrinsicCallDef::Encoded { origin, expr_call } => {
			let mut expr_call = expr_call.clone();

			// remove first arg from expr_call
			let mut final_args = Punctuated::<Expr, Comma>::new();
			let args: Vec<&Expr> = expr_call.args.iter().collect();
			for arg in &args[1..] {
				final_args.push((*(*arg)).clone());
			}
			expr_call.args = final_args;

			// modify extrinsic call to be prefixed with new_call_variant
			if let Expr::Path(expr_path) = &mut *expr_call.func {
				if let Some(segment) = expr_path.path.segments.last_mut() {
					segment.ident = Ident::new(
						format!("new_call_variant_{}", segment.ident.to_string()).as_str(),
						Span::call_site(),
					);
				}
			}
			// (pre_call, post_call):
			(
				quote! {
					let __call = Call::<#generics>::#expr_call;
					let __benchmarked_call_encoded = #codec::Encode::encode(&__call);
				},
				quote! {
					let __call_decoded = <Call<#generics> as #codec::Decode>
						::decode(&mut &__benchmarked_call_encoded[..])
						.expect("call is encoded above, encoding must be correct");
					let __origin = #origin.into();
					<Call<#generics> as #traits::UnfilteredDispatchable>::dispatch_bypass_filter(
						__call_decoded,
						__origin,
					)?;
				},
			)
		},
		ExtrinsicCallDef::Block(block) => (quote!(), quote!(#block)),
	};

	// generate final quoted tokens
	let res = quote! {
		// compile-time assertions that each referenced param type implements ParamRange
		#(
			#home::assert_impl_all!(#param_types: #home::ParamRange);
		)*

		#[allow(non_camel_case_types)]
		struct #name;

		#[allow(unused_variables)]
		impl<#full_generics> #krate::BenchmarkingSetup<#generics>
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

				// benchmark setup code (stuff before #[extrinsic_call])
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
					Ok(())
				}))
			}
		}

		#[cfg(test)]
		impl<#full_generics> Pallet<#generics> where T: ::frame_system::Config, #where_clause {
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
