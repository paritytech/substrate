// Copyright 2017-2020 Parity Technologies (UK) Ltd.
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

//! Miscellaneous additional datatypes.

use codec::{Encode, Decode};
use sp_runtime::RuntimeDebug;
use crate::vote_threshold::VoteThreshold;

/// Info regarding an ongoing referendum.
#[derive(Encode, Decode, Clone, PartialEq, Eq, RuntimeDebug)]
pub struct ReferendumInfo<BlockNumber, Hash> {
	/// When voting on this referendum will end.
	pub (crate) end: BlockNumber,
	/// The hash of the proposal being voted on.
	pub (crate) proposal_hash: Hash,
	/// The thresholding mechanism to determine whether it passed.
	pub (crate) threshold: VoteThreshold,
	/// The delay (in blocks) to wait after a successful referendum before deploying.
	pub (crate) delay: BlockNumber,
}

impl<BlockNumber, Hash> ReferendumInfo<BlockNumber, Hash> {
	/// Create a new instance.
	pub fn new(
		end: BlockNumber,
		proposal_hash: Hash,
		threshold: VoteThreshold,
		delay: BlockNumber
	) -> Self {
		ReferendumInfo { end, proposal_hash, threshold, delay }
	}
}

/// State of a proxy voting account.
#[derive(Clone, Eq, PartialEq, Encode, Decode, RuntimeDebug)]
pub enum ProxyState<AccountId> {
	/// Account is open to becoming a proxy but is not yet assigned.
	Open(AccountId),
	/// Account is actively being a proxy.
	Active(AccountId),
}

impl<AccountId> ProxyState<AccountId> {
	pub (crate) fn as_active(self) -> Option<AccountId> {
		match self {
			ProxyState::Active(a) => Some(a),
			ProxyState::Open(_) => None,
		}
	}
}
