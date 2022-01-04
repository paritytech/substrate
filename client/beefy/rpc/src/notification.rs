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

use codec::Encode;
use serde::{Deserialize, Serialize};

use sp_runtime::traits::Block as BlockT;

/// An encoded signed commitment proving that the given header has been finalized.
/// The given bytes should be the SCALE-encoded representation of a
/// `beefy_primitives::SignedCommitment`.
#[derive(Clone, Serialize, Deserialize)]
pub struct SignedCommitment(sp_core::Bytes);

impl SignedCommitment {
	pub fn new<Block>(
		signed_commitment: beefy_gadget::notification::SignedCommitment<Block>,
	) -> Self
	where
		Block: BlockT,
	{
		SignedCommitment(signed_commitment.encode().into())
	}
}
