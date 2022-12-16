use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{
	parse::{Parse, ParseStream},
	parse_macro_input,
	spanned::Spanned,
	token::Token,
	Block, Expr, ExprCall, Item, ItemFn, ItemMod, Stmt,
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
	setup_stmts: Vec<Stmt>,
	extrinsic_call_stmt: Stmt,
	extrinsic_call_fn: ExprCall,
	verify_stmts: Vec<Stmt>,
}

impl BenchmarkDef {
	pub fn from(item_fn: &ItemFn) -> Option<BenchmarkDef> {
		let mut i = 0;
		for child in &item_fn.block.stmts {
			if let Stmt::Semi(Expr::Call(fn_call), token) = child {
				let i = 0;
				for attr in &fn_call.attrs {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							let mut fn_call_copy = fn_call.clone();
							fn_call_copy.attrs.pop(); // consume #[extrinsic call]
							return Some(BenchmarkDef {
								setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
								extrinsic_call_stmt: Stmt::Semi(
									Expr::Call(fn_call.clone()),
									token.clone(),
								),
								extrinsic_call_fn: fn_call.clone(),
								verify_stmts: Vec::from(
									&item_fn.block.stmts[i..item_fn.block.stmts.len()],
								),
							})
						}
					}
				}
			}
			i += 1;
		}
		return None
	}
}

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
	let mut benchmark_def = match BenchmarkDef::from(&item_fn) {
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
