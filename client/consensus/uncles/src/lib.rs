// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Uncles functionality for Substrate.
#![forbid(unsafe_code, missing_docs)]

use sp_consensus::SelectChain;
use sp_inherents::{InherentDataProviders};
use log::warn;
use sc_client_api::ProvideUncles;
use sp_runtime::traits::{Block as BlockT, Header};
use std::sync::Arc;
use sp_authorship;

/// Maximum uncles generations we may provide to the runtime.
const MAX_UNCLE_GENERATIONS: u32 = 8;

/// Register uncles inherent data provider, if not registered already.
pub fn register_uncles_inherent_data_provider<B, C, SC>(
	client: Arc<C>,
	select_chain: SC,
	inherent_data_providers: &InherentDataProviders,
) -> Result<(), sp_consensus::Error> where
	B: BlockT,
	C: ProvideUncles<B> + Send + Sync + 'static,
	SC: SelectChain<B> + 'static,
{
	if !inherent_data_providers.has_provider(&sp_authorship::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(sp_authorship::InherentDataProvider::new(move || {
				{
					let chain_head = match select_chain.best_chain() {
						Ok(x) => x,
						Err(e) => {
							warn!(target: "uncles", "Unable to get chain head: {:?}", e);
							return Vec::new();
						}
					};
					match client.uncles(chain_head.hash(), MAX_UNCLE_GENERATIONS.into()) {
						Ok(uncles) => uncles,
						Err(e) => {
							warn!(target: "uncles", "Unable to get uncles: {:?}", e);
							Vec::new()
						}
					}
				}
			}))
		.map_err(|err| sp_consensus::Error::InherentData(err.into()))?;
	}
	Ok(())
}

