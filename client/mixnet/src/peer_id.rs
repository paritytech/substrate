// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use libp2p_identity::PeerId;
use mixnet::core::PeerId as CorePeerId;

/// Convert a libp2p [`PeerId`] into a mixnet core [`PeerId`](CorePeerId).
///
/// This will succeed only if `peer_id` is an Ed25519 public key ("hashed" using the identity
/// hasher). Returns `None` on failure.
pub fn to_core_peer_id(peer_id: &PeerId) -> Option<CorePeerId> {
	let hash = peer_id.as_ref();
	if hash.code() != 0 {
		// Hash is not identity
		return None
	}
	let public = libp2p_identity::PublicKey::try_decode_protobuf(hash.digest()).ok()?;
	public.try_into_ed25519().ok().map(|public| public.to_bytes())
}

/// Convert a mixnet core [`PeerId`](CorePeerId) into a libp2p [`PeerId`].
///
/// This will succeed only if `peer_id` represents a point on the Ed25519 curve. Returns `None` on
/// failure.
pub fn from_core_peer_id(core_peer_id: &CorePeerId) -> Option<PeerId> {
	let public = libp2p_identity::ed25519::PublicKey::try_from_bytes(core_peer_id).ok()?;
	let public: libp2p_identity::PublicKey = public.into();
	Some(public.into())
}
