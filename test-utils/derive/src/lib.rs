// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro_attribute]
pub fn test(args: TokenStream, item: TokenStream) -> TokenStream {
	impl_test(args, item)
}

fn impl_test(args: TokenStream, item: TokenStream) -> TokenStream {
	let input = syn::parse_macro_input!(item as syn::ItemFn);
	let args = syn::parse_macro_input!(args as syn::AttributeArgs);

	parse_knobs(input, args).unwrap_or_else(|e| e.to_compile_error().into())
}

fn parse_knobs(
	mut input: syn::ItemFn,
	args: syn::AttributeArgs,
) -> Result<TokenStream, syn::Error> {
	let sig = &mut input.sig;
	let body = &input.block;
	let attrs = &input.attrs;
	let vis = input.vis;

	if sig.inputs.len() != 1 {
		let msg = "the test function accepts only one argument of type sc_service::TaskExecutor";
		return Ok(syn::Error::new_spanned(&sig, msg).to_compile_error().into());
	}
	let (task_executor_name, task_executor_type) = match sig.inputs.pop().map(|x| x.into_value()) {
		Some(syn::FnArg::Typed(x)) => (x.pat, x.ty),
		_ => {
			let msg =
				"the test function accepts only one argument of type sc_service::TaskExecutor";
			return Ok(syn::Error::new_spanned(&sig, msg).to_compile_error().into());
		}
	};

	let header = {
		quote! {
			#[tokio::test(#(#args)*)]
		}
	};

	let result = quote! {
		#header
		#(#attrs)*
		#vis #sig {
			use futures::future::FutureExt;

			let #task_executor_name: #task_executor_type = (|fut, _| {
				tokio::spawn(fut).map(drop)
			})
			.into();
			let timeout_task = tokio::time::delay_for(
				std::time::Duration::from_secs(
					std::env::var("SUBSTRATE_TEST_TIMEOUT")
						.ok()
						.and_then(|x| x.parse().ok())
						.unwrap_or(600))
			).fuse();
			let actual_test_task = async move {
				#body
			}
			.fuse();

			futures::pin_mut!(timeout_task, actual_test_task);

			futures::select! {
				_ = timeout_task => {
					panic!("the test took too long");
				},
				_ = actual_test_task => {},
			}
		}
	};

	Ok(result.into())
}
