// This file is part of Substrate.

// Copyright (C) 2021-2022 Parity Technologies (UK) Ltd.
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

//! BEEFY justifications sync support.

use sc_network_common::sync::beefy::{BeefyEncodedProof, BeefyJustifRequest};
use sp_blockchain::HeaderBackend;
use sp_runtime::traits::{Block as BlockT, NumberFor, Zero};
use std::sync::Arc;

type BeefyValidatorSet = beefy_primitives::ValidatorSet<beefy_primitives::crypto::AuthorityId>;

/// Import BEEFY proof result.
pub enum BeefyProofImportResult {
	/// Import was successful.
	Success,
	/// Bad proof.
	BadResponse,
}

/// BEEFY justifications sync.
pub struct BeefySync<B: BlockT, Client> {
	client: Arc<Client>,
	validator_set: BeefyValidatorSet,
	last_number: NumberFor<B>,
}

impl<B, Client> BeefySync<B, Client>
where
	B: BlockT,
	Client: HeaderBackend<B> + 'static,
{
	///  Create a new instance.
	pub fn new(client: Arc<Client>) -> Self {
		Self {
			client,
			// FIXME: use right BEEFY ValidatorSet from gadget or client.
			validator_set: BeefyValidatorSet::new(Vec::new().into_iter(), 0).unwrap(),
			last_number: Zero::zero(),
		}
	}

	///  Validate and import a BEEFY proof response.
	pub fn import_beefy_proof(&mut self, _response: BeefyEncodedProof) -> BeefyProofImportResult {
		// TODO: implement:
		BeefyProofImportResult::Success
	}

	/// Produce next BEEFY proof request.
	pub fn next_beefy_proof_request(&self) -> Option<BeefyJustifRequest<B>> {
		// TODO: get this from BEEFY worker.
		Some(BeefyJustifRequest { begin: self.last_number })
	}
}
