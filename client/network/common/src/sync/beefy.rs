// Copyright 2022 Parity Technologies (UK) Ltd.
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

use codec::{Decode, Encode};
use sp_runtime::traits::{Block, NumberFor};

pub const BEEFY_LOG_TARGET: &str = "beefy::sync";

/// Scale-encoded BEEFY justification response.
pub struct BeefyEncodedProof(pub Vec<u8>);

/// BEEFY justification request.
#[derive(Encode, Decode, Debug)]
pub struct BeefyJustifRequest<B: Block> {
	/// Start collecting proofs from this block.
	pub begin: NumberFor<B>,
}
