// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
use proc_macro2::Span;
use proc_macro_crate::{crate_name, FoundCrate};
use quote::quote;
use syn::{Error, Expr, Ident, ItemFn};

/// Add a log prefix to the function.
///
/// This prefixes all the log lines with `[<name>]` (after the timestamp). It works by making a
/// tracing's span that is propagated to all the child calls and child tasks (futures) if they are
/// spawned properly with the `SpawnHandle` (see `TaskManager` in sc-cli) or if the futures use
/// `.in_current_span()` (see tracing-futures).
///
/// See Tokio's [tracing documentation](https://docs.rs/tracing-core/) and
/// [tracing-futures documentation](https://docs.rs/tracing-futures/) for more details.
///
/// # Implementation notes
///
/// If there are multiple spans with a log prefix, only the latest will be shown.
///
/// # Example with a literal
///
/// ```ignore
/// Builds a new service for a light client.
/// #[sc_cli::prefix_logs_with("light")]
/// pub fn new_light(config: Configuration) -> Result<TaskManager, ServiceError> {
///     let (client, backend, keystore, mut task_manager, on_demand) =
///         sc_service::new_light_parts::<Block, RuntimeApi, Executor>(&config)?;
///
///        ...
/// }
/// ```
///
/// Will produce logs that look like this:
///
/// ```text
/// 2020-10-16 08:03:14  Substrate Node
/// 2020-10-16 08:03:14  ✌️  version 2.0.0-47f7d3f2e-x86_64-linux-gnu
/// 2020-10-16 08:03:14  ❤️  by Anonymous, 2017-2020
/// 2020-10-16 08:03:14  📋 Chain specification: Local Testnet
/// 2020-10-16 08:03:14  🏷  Node name: nice-glove-1401
/// 2020-10-16 08:03:14  👤 Role: LIGHT
/// 2020-10-16 08:03:14  💾 Database: RocksDb at /tmp/substrate95w2Dk/chains/local_testnet/db
/// 2020-10-16 08:03:14  ⛓  Native runtime: node-template-1 (node-template-1.tx1.au1)
/// 2020-10-16 08:03:14  [light] 🔨 Initializing Genesis block/state (state: 0x121d…8e36, header-hash: 0x24ef…8ff6)
/// 2020-10-16 08:03:14  [light] Loading GRANDPA authorities from genesis on what appears to be first startup.
/// 2020-10-16 08:03:15  [light] ⏱  Loaded block-time = 6000 milliseconds from genesis on first-launch
/// 2020-10-16 08:03:15  [light] Using default protocol ID "sup" because none is configured in the chain specs
/// 2020-10-16 08:03:15  [light] 🏷  Local node identity is: 12D3KooWHX4rkWT6a6N55Km7ZnvenGdShSKPkzJ3yj9DU5nqDtWR
/// 2020-10-16 08:03:15  [light] 📦 Highest known block at #0
/// 2020-10-16 08:03:15  [light] 〽️ Prometheus server started at 127.0.0.1:9615
/// 2020-10-16 08:03:15  [light] Listening for new connections on 127.0.0.1:9944.
/// ```
///
/// # Example using the actual node name
///
/// ```ignore
/// Builds a new service for a light client.
/// #[sc_cli::prefix_logs_with(config.network.node_name.as_str())]
/// pub fn new_light(config: Configuration) -> Result<TaskManager, ServiceError> {
///     let (client, backend, keystore, mut task_manager, on_demand) =
///         sc_service::new_light_parts::<Block, RuntimeApi, Executor>(&config)?;
///
///        ...
/// }
/// ```
///
/// Will produce logs that look like this:
///
/// ```text
/// 2020-10-16 08:12:57  Substrate Node
/// 2020-10-16 08:12:57  ✌️  version 2.0.0-efb9b822a-x86_64-linux-gnu
/// 2020-10-16 08:12:57  ❤️  by Anonymous, 2017-2020
/// 2020-10-16 08:12:57  📋 Chain specification: Local Testnet
/// 2020-10-16 08:12:57  🏷  Node name: open-harbor-1619
/// 2020-10-16 08:12:57  👤 Role: LIGHT
/// 2020-10-16 08:12:57  💾 Database: RocksDb at /tmp/substrate9T9Mtb/chains/local_testnet/db
/// 2020-10-16 08:12:57  ⛓  Native runtime: node-template-1 (node-template-1.tx1.au1)
/// 2020-10-16 08:12:58  [open-harbor-1619] 🔨 Initializing Genesis block/state (state: 0x121d…8e36, header-hash: 0x24ef…8ff6)
/// 2020-10-16 08:12:58  [open-harbor-1619] Loading GRANDPA authorities from genesis on what appears to be first startup.
/// 2020-10-16 08:12:58  [open-harbor-1619] ⏱  Loaded block-time = 6000 milliseconds from genesis on first-launch
/// 2020-10-16 08:12:58  [open-harbor-1619] Using default protocol ID "sup" because none is configured in the chain specs
/// 2020-10-16 08:12:58  [open-harbor-1619] 🏷  Local node identity is: 12D3KooWRzmYC8QTK1Pm8Cfvid3skTS4Hn54jc4AUtje8Rqbfgtp
/// 2020-10-16 08:12:58  [open-harbor-1619] 📦 Highest known block at #0
/// 2020-10-16 08:12:58  [open-harbor-1619] 〽️ Prometheus server started at 127.0.0.1:9615
/// 2020-10-16 08:12:58  [open-harbor-1619] Listening for new connections on 127.0.0.1:9944.
/// ```
#[proc_macro_attribute]
pub fn prefix_logs_with(arg: TokenStream, item: TokenStream) -> TokenStream {
	let item_fn = syn::parse_macro_input!(item as ItemFn);

	if arg.is_empty() {
		return Error::new(
			Span::call_site(),
			"missing argument: name of the node. Example: sc_cli::prefix_logs_with(<expr>)",
		)
		.to_compile_error()
		.into()
	}

	let name = syn::parse_macro_input!(arg as Expr);

	let crate_name = match crate_name("sc-tracing") {
		Ok(FoundCrate::Itself) => Ident::from(Ident::new("sc_tracing", Span::call_site())),
		Ok(FoundCrate::Name(crate_name)) => Ident::new(&crate_name, Span::call_site()),
		Err(e) => return Error::new(Span::call_site(), e).to_compile_error().into(),
	};

	let ItemFn { attrs, vis, sig, block } = item_fn;

	(quote! {
		#(#attrs)*
		#vis #sig {
			let span = #crate_name::tracing::info_span!(
				#crate_name::logging::PREFIX_LOG_SPAN,
				name = #name,
			);
			let _enter = span.enter();

			#block
		}
	})
	.into()
}
