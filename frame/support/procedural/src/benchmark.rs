use derive_syn_parse::Parse;
use proc_macro::TokenStream;
use proc_macro2::{Ident, Span, TokenStream as TokenStream2};
use quote::{quote, ToTokens};
use syn::{
	parse_macro_input,
	punctuated::Punctuated,
	spanned::Spanned,
	token::{Comma, Gt, Lt},
	Error, Expr, ExprCall, FnArg, ItemFn, ItemMod, LitInt, Pat, Result, Stmt, Type,
};

mod keywords {
	syn::custom_keyword!(extrinsic_call);
}

fn emit_error<T: Into<TokenStream> + Clone, S: Into<String>>(item: &T, message: S) -> TokenStream {
	let item = Into::<TokenStream>::into(item.clone());
	let message = Into::<String>::into(message);
	let span = proc_macro2::TokenStream::from(item).span();
	return syn::Error::new(span, message).to_compile_error().into()
}

#[derive(Debug, Clone, PartialEq)]
struct ParamDef {
	name: String,
	typ: Type,
	start: u32,
	end: u32,
}

#[derive(Parse)]
struct RangeArgs {
	_lt_token: Lt,
	start: LitInt,
	_comma: Comma,
	end: LitInt,
	_gt_token: Gt,
}

struct BenchmarkDef {
	params: Vec<ParamDef>,
	setup_stmts: Vec<Stmt>,
	extrinsic_call: ExprCall,
	origin: Expr,
	verify_stmts: Vec<Stmt>,
}

impl BenchmarkDef {
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

pub fn benchmarks(_attrs: TokenStream, tokens: TokenStream) -> TokenStream {
	let item_mod = parse_macro_input!(tokens as ItemMod);
	let contents = match item_mod.content {
		Some(content) => content.1,
		None =>
			return emit_error(
				&item_mod.to_token_stream(),
				"#[frame_support::benchmarks] can only be applied to a non-empty module.",
			),
	};
	let mod_ident = item_mod.ident;
	quote! {
		#[cfg(any(feature = "runtime-benchmarks", test))]
		mod #mod_ident {
			#(#contents)
			*
		}
	}
	.into()
}

// prepares a `Vec<ParamDef>` to be interpolated by `quote!`
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

pub fn benchmark(_attrs: TokenStream, tokens: TokenStream, is_instance: bool) -> TokenStream {
	// parse attached item as a function def
	let item_fn = parse_macro_input!(tokens as ItemFn);

	// build a BenchmarkDef from item_fn
	let benchmark_def = match BenchmarkDef::from(&item_fn) {
		Ok(def) => def,
		Err(err) => return err.to_compile_error().into(),
	};

	// set up variables needed during quoting
	let name = item_fn.sig.ident;
	let krate = quote!(::frame_benchmarking);
	let home = quote!(::frame_support);
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
	println!("{}", res.to_string());
	res.into()
}
