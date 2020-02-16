// Copyright 2019-2020 Parity Technologies (UK) Ltd.
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

//! Sassafras authority selection and slot claiming.

use sp_consensus_sassafras::{
	SlotNumber, AuthorityPair, SassafrasConfiguration
};
use sp_consensus_sassafras::digests::PreDigest;
use sc_keystore::KeyStorePtr;
use super::Epoch;

/// Tries to claim the given slot number. This method starts by trying to claim
/// a primary VRF based slot. If we are not able to claim it, then if we have
/// secondary slots enabled for the given epoch, we will fallback to trying to
/// claim a secondary slot.
pub(super) fn claim_slot(
	slot_number: SlotNumber,
	epoch: &Epoch,
	config: &SassafrasConfiguration,
	keystore: &KeyStorePtr,
) -> Option<(PreDigest, AuthorityPair)> {
	None
}
