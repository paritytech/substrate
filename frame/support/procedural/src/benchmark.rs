use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{
	parse::{Parse, ParseStream},
	parse_macro_input,
	punctuated::Punctuated,
	spanned::Spanned,
	token::{Comma, Gt, Lt},
	Block, Error, Expr, ExprCall, FnArg, Item, ItemFn, LitInt, Pat, Result, Stmt, Type,
};

mod keywords {
	syn::custom_keyword!(extrinsic_call);
	syn::custom_keyword!(cfg);
	syn::custom_keyword!(benchmark);
	syn::custom_keyword!(instance_benchmark);
}

/// Represents a "bare" block, that is, a the contents of a [`Block`] minus the curly braces.
/// Useful for parsing the contents of a decl macro that takes a block, since the curly braces
/// are not actually included in the input [`TokenStream`] in that scenario. The contents are
/// parsed as a [`Vec<Stmt>`] called `stmts`. Can be used with [`parse_macro_input!`], etc.
struct BareBlock {
	stmts: Vec<Stmt>,
}

impl Parse for BareBlock {
	fn parse(input: ParseStream) -> syn::Result<Self> {
		match Block::parse_within(input) {
			Ok(stmts) => Ok(BareBlock { stmts }),
			Err(e) => Err(e),
		}
	}
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

/// Represents a parsed `#[benchmark]` or `#[instance_banchmark]` item.
#[derive(Clone)]
struct BenchmarkDef {
	params: Vec<ParamDef>,
	setup_stmts: Vec<Stmt>,
	extrinsic_call: ExprCall,
	origin: Expr,
	verify_stmts: Vec<Stmt>,
}

impl BenchmarkDef {
	/// Constructs a [`BenchmarkDef`] by traversing an existing [`ItemFn`] node.
	pub fn from(item_fn: &ItemFn) -> Result<BenchmarkDef> {
		let mut i = 0; // index of child
		let mut params: Vec<ParamDef> = Vec::new();
		for arg in &item_fn.sig.inputs {
			// parse params such as "x: Linear<0, 1>"
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
		for child in &item_fn.block.stmts {
			// find #[extrinsic_call] annotation and build up the setup, call, and verify
			// blocks based on the location of this annotation
			if let Stmt::Semi(Expr::Call(fn_call), _token) = child {
				let mut k = 0; // index of attr
				for attr in &fn_call.attrs {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							let mut extrinsic_call = fn_call.clone();
							extrinsic_call.attrs.remove(k); // consume #[extrinsic call]
							let origin = match extrinsic_call.args.first() {
								Some(arg) => arg.clone(),
								None => return Err(Error::new(
									extrinsic_call.args.span(),
									"Extrinsic call must specify its origin as the first argument.",
								)),
							};
							let mut final_args = Punctuated::<Expr, Comma>::new();
							let args: Vec<&Expr> = extrinsic_call.args.iter().collect();
							for arg in &args[1..] {
								final_args.push((*(*arg)).clone());
							}
							extrinsic_call.args = final_args;
							return Ok(BenchmarkDef {
								params,
								setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
								extrinsic_call,
								origin,
								verify_stmts: Vec::from(
									&item_fn.block.stmts[(i + 1)..item_fn.block.stmts.len()],
								),
							})
						}
					}
					k += 1;
				}
			}
			i += 1;
		}
		return Err(Error::new(
			item_fn.block.brace_token.span,
			"Missing #[extrinsic_call] annotation in benchmark function body.",
		))
	}
}

pub fn benchmarks(tokens: TokenStream) -> TokenStream {
	let mut block = parse_macro_input!(tokens as BareBlock);
	let mut expanded_stmts: Vec<TokenStream2> = Vec::new();
	let mut benchmark_defs: Vec<BenchmarkDef> = Vec::new();
	let mut benchmark_names: Vec<Ident> = Vec::new();
	let mut any_instance = false;
	for stmt in &mut block.stmts {
		let mut found_item: Option<(ItemFn, bool)> = None;
		if let Stmt::Item(stmt) = stmt {
			if let Item::Fn(func) = stmt {
				let mut i = 0;
				for attr in &func.attrs.clone() {
					let mut consumed = false;
					if let Some(seg) = attr.path.segments.last() {
						if let Ok(_) =
							syn::parse::<keywords::benchmark>(seg.ident.to_token_stream().into())
						{
							consumed = true;
							func.attrs.remove(i);
							found_item = Some((func.clone(), false));
						} else if let Ok(_) = syn::parse::<keywords::instance_benchmark>(
							seg.ident.to_token_stream().into(),
						) {
							consumed = true;
							func.attrs.remove(i);
							found_item = Some((func.clone(), true));
							any_instance = true;
						}
					}
					if !consumed {
						i += 1;
					}
				}
			}
		}
		if let Some((item_fn, is_instance)) = found_item {
			// this item is a #[benchmark] or #[instance_benchmark]

			// build a BenchmarkDef from item_fn
			let benchmark_def = match BenchmarkDef::from(&item_fn) {
				Ok(def) => def,
				Err(err) => return err.to_compile_error().into(),
			};

			// expand benchmark_def
			let expanded = expand_benchmark(benchmark_def.clone(), &item_fn.sig.ident, is_instance);
			benchmark_names.push(item_fn.sig.ident.clone());

			expanded_stmts.push(expanded);
			benchmark_defs.push(benchmark_def);
		} else {
			// this is not a benchmark item, copy it in verbatim
			expanded_stmts.push(stmt.to_token_stream());
		}
	}

	// TODO: components() after SelectedBenchmark

	let generics = match any_instance {
		false => quote!(T),
		true => quote!(T, I),
	};
	let full_generics = match any_instance {
		false => quote!(T: Config),
		true => quote!(T: Config<I>, I: 'static),
	};
	let krate = quote!(::frame_benchmarking);

	let res = quote! {
		#(#expanded_stmts)
		*

		#[allow(non_camel_case_types)]
		enum SelectedBenchmark {
			#(#benchmark_names),
			*
		}

		impl<#full_generics> #krate::BenchmarkingSetup<#generics> for SelectedBenchmark {
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
		}
	};
	println!("{}", res.to_string());
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

fn expand_benchmark(benchmark_def: BenchmarkDef, name: &Ident, is_instance: bool) -> TokenStream2 {
	// set up variables needed during quoting
	let krate = quote!(::frame_benchmarking);
	let home = quote!(::frame_support::benchmarking);
	let codec = quote!(#krate::frame_support::codec);
	let traits = quote!(#krate::frame_support::traits);
	let setup_stmts = benchmark_def.setup_stmts;
	let mut extrinsic_call = benchmark_def.extrinsic_call;
	let origin = benchmark_def.origin;
	let verify_stmts = benchmark_def.verify_stmts;

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

	// modify extrinsic call to be prefixed with new_call_variant
	if let Expr::Path(expr_path) = &mut *extrinsic_call.func {
		if let Some(segment) = expr_path.path.segments.last_mut() {
			segment.ident = Ident::new(
				format!("new_call_variant_{}", segment.ident.to_string()).as_str(),
				Span::call_site(),
			);
		} // else handle error?
	} // else handle error?

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
		for #name {
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
				let __call = Call::<#generics>::#extrinsic_call;
				let __benchmarked_call_encoded = #codec::Encode::encode(&__call);
				Ok(#krate::Box::new(move || -> Result<(), #krate::BenchmarkError> {
					let __call_decoded = <Call<#generics> as #codec::Decode>
						::decode(&mut &__benchmarked_call_encoded[..])
						.expect("call is encoded above, encoding must be correct");
					let __origin = #origin.into();
					<Call<#generics> as #traits::UnfilteredDispatchable>::dispatch_bypass_filter(
						__call_decoded,
						__origin,
					)?;
					if verify {
						#(
							#verify_stmts
						)*
					}
					Ok(())
				}))
			}
		}
	};
	res
}

pub fn benchmark(_attrs: TokenStream, tokens: TokenStream, is_instance: bool) -> TokenStream {
	// parse attached item as a function def
	let item_fn = parse_macro_input!(tokens as ItemFn);

	// build a BenchmarkDef from item_fn
	let benchmark_def = match BenchmarkDef::from(&item_fn) {
		Ok(def) => def,
		Err(err) => return err.to_compile_error().into(),
	};

	expand_benchmark(benchmark_def, &item_fn.sig.ident, is_instance).into()
}
