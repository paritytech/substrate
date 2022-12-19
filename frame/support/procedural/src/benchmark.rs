use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
	parse::{Parse, ParseStream},
	parse_macro_input,
	spanned::Spanned,
	Block, Expr, ExprCall, FnArg, ItemFn, ItemMod, Pat, Stmt, Type,
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

struct BenchmarkDef {
	//           name,   typ,    A,   B
	params: Vec<(String, String, u32, u32)>,
	setup_stmts: Vec<Stmt>,
	extrinsic_call_stmt: Stmt,
	extrinsic_call_fn: ExprCall,
	verify_stmts: Vec<Stmt>,
}

impl BenchmarkDef {
	pub fn from(item_fn: &ItemFn) -> Option<BenchmarkDef> {
		let mut i = 0; // index of child
		let params: Vec<(String, String, u32, u32)> = Vec::new();
		for arg in &item_fn.sig.inputs {
			// parse params such as "x: Linear<0, 1>"
			let mut name: Option<String> = None;
			let mut typ: Option<&Type> = None;
			if let FnArg::Typed(arg) = arg {
				if let Pat::Ident(ident) = &*arg.pat {
					name = Some(ident.ident.to_token_stream().to_string());
				}
				typ = Some(&*arg.ty);
			}
			if let (Some(name), Some(typ)) = (name, typ) {
				// test
				println!("name: {:?}", name);
				println!("type: {:?}", typ);
			} else {
			}
		}
		for child in &item_fn.block.stmts {
			// find #[extrinsic_call] annotation and build up the setup, call, and verify
			// blocks based on the location of this annotation
			if let Stmt::Semi(Expr::Call(fn_call), token) = child {
				let mut k = 0; // index of attr
				for attr in &fn_call.attrs {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							let mut fn_call_copy = fn_call.clone();
							fn_call_copy.attrs.remove(k); // consume #[extrinsic call]
							return Some(BenchmarkDef {
								params,
								setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
								extrinsic_call_stmt: Stmt::Semi(
									Expr::Call(fn_call_copy.clone()),
									token.clone(),
								),
								extrinsic_call_fn: fn_call_copy,
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
		return None
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

pub fn benchmark(_attrs: TokenStream, tokens: TokenStream) -> TokenStream {
	let item_fn = parse_macro_input!(tokens as ItemFn);
	let benchmark_def = match BenchmarkDef::from(&item_fn) {
		Some(def) => def,
		None =>
			return emit_error(
				&item_fn.block.to_token_stream(),
				"Missing #[extrinsic_call] annotation in benchmark function body.",
			),
	};
	let name = item_fn.sig.ident;
	let krate = quote!(::frame_benchmarking);
	let setup_stmts = benchmark_def.setup_stmts;
	let extrinsic_call_stmt = benchmark_def.extrinsic_call_stmt;
	let verify_stmts = benchmark_def.verify_stmts;
	let params = vec![quote!(x, 0, 1)];
	let param_names = vec![quote!(x)];
	quote! {
		use ::frame_support::assert_impl_all;
		assert_impl_all!(::frame_support::Linear<0, 1>: ::frame_support::ParamRange);

		#[allow(non_camel_case_types)]
		struct #name;

		#[allow(unused_variables)]
		impl<T: Config> ::frame_benchmarking::BenchmarkingSetup<T>
		for #name {
			fn components(&self) -> #krate::Vec<(#krate::BenchmarkParameter, u32, u32)> {
				#krate::vec! [
					#(
						(#krate::BenchmarkParameter::#params)
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

				// TODO: figure out parameter parsing:
				// $(
				// 	let $pre_id : $pre_ty = $pre_ex;
				// )*
				// $( $param_instancer ; )*
				// $( $post )*

				// benchmark setup code (stuff before #[extrinsic_call])
				#(
					#setup_stmts
				)*

				Ok(#krate::Box::new(move || -> Result<(), #krate::BenchmarkError> {
					#extrinsic_call_stmt
					if verify {
						#(
							#verify_stmts
						)*
					}
					Ok(())
				}))
			}
		}
	}
	.into()
}
