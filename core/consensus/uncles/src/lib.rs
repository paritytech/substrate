// Copyright 2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Uncles functionality for Substrate.
//!
#![deny(warnings)]
#![forbid(unsafe_code, missing_docs)]

use consensus_common::SelectChain;
use inherents::{InherentDataProviders};
use log::warn;
use client::ProvideUncles;
use sr_primitives::traits::{Block as BlockT, Header};
use std::sync::Arc;

/// Maximum uncles generations we may provide to the runtime.
const MAX_UNCLE_GENERATIONS: u32 = 8;

/// Register uncles inherent data provider, if not registered already.
pub fn register_uncles_inherent_data_provider<B, C, SC>(
	client: Arc<C>,
	select_chain: SC,
	inherent_data_providers: &InherentDataProviders,
) -> Result<(), consensus_common::Error> where
	B: BlockT,
	C: ProvideUncles<B> + Send + Sync + 'static,
	SC: SelectChain<B> + 'static,
{
	if !inherent_data_providers.has_provider(&srml_authorship::INHERENT_IDENTIFIER) {
		inherent_data_providers
			.register_provider(srml_authorship::InherentDataProvider::new(move || {
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
		.map_err(|err| consensus_common::Error::InherentData(err.into()))?;
	}
	Ok(())
}

