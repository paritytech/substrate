use proc_macro::TokenStream;
use quote::{quote, ToTokens};
use syn::{parse_macro_input, spanned::Spanned, Expr, ExprCall, ItemFn, Stmt};

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
	extrinsic_call: ExprCall,
	verify_stmts: Vec<Stmt>,
}

impl BenchmarkDef {
	pub fn from(item_fn: &ItemFn) -> Option<BenchmarkDef> {
		let mut i = 0;
		for child in &item_fn.block.stmts {
			if let Stmt::Semi(Expr::Call(fn_call), _) = child {
				for attr in &fn_call.attrs {
					if let Some(segment) = attr.path.segments.last() {
						if let Ok(_) = syn::parse::<keywords::extrinsic_call>(
							segment.ident.to_token_stream().into(),
						) {
							//let setup_stmts = &item_fn.block.stmts[0..i];
							return Some(BenchmarkDef {
								setup_stmts: Vec::from(&item_fn.block.stmts[0..i]),
								extrinsic_call: fn_call.clone(),
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

pub fn benchmark(_attrs: TokenStream, tokens: TokenStream) -> TokenStream {
	let item_fn = parse_macro_input!(tokens as ItemFn);
	if let Some(_benchmark_def) = BenchmarkDef::from(&item_fn) {
		// todo
	} else {
		return emit_error(
			&item_fn.block.to_token_stream(),
			"Missing #[extrinsic_call] annotation in benchmark function body.",
		)
	}
	return quote!().into()
}
