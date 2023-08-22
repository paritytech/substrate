// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Mixnet types used by both host and runtime.

use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_std::vec::Vec;

mod app {
	use sp_application_crypto::{app_crypto, key_types::MIXNET, sr25519};
	app_crypto!(sr25519, MIXNET);
}

/// Authority public session key, used to verify registration signatures.
pub type AuthorityId = app::Public;
/// Authority signature, attached to mixnode registrations.
pub type AuthoritySignature = app::Signature;

/// Absolute session index.
pub type SessionIndex = u32;

/// Each session should progress through these phases in order.
#[derive(Decode, Encode, TypeInfo, PartialEq, Eq)]
pub enum SessionPhase {
	/// Generate cover traffic to the current session's mixnode set.
	CoverToCurrent,
	/// Build requests using the current session's mixnode set.
	RequestsToCurrent,
	/// Only send cover (and forwarded) traffic to the previous session's mixnode set.
	CoverToPrev,
	/// Disconnect the previous session's mixnode set.
	DisconnectFromPrev,
}

/// The index and phase of the current session.
#[derive(Decode, Encode, TypeInfo)]
pub struct SessionStatus {
	/// Index of the current session.
	pub current_index: SessionIndex,
	/// Current session phase.
	pub phase: SessionPhase,
}

/// Size in bytes of a [`KxPublic`].
pub const KX_PUBLIC_SIZE: usize = 32;

/// X25519 public key, used in key exchange between message senders and mixnodes. Mixnode public
/// keys are published on-chain and change every session. Message senders generate a new key for
/// every message they send.
pub type KxPublic = [u8; KX_PUBLIC_SIZE];

/// Ed25519 public key of a libp2p peer.
pub type PeerId = [u8; 32];

/// Information published on-chain for each mixnode every session.
#[derive(Decode, Encode, TypeInfo)]
pub struct Mixnode {
	/// Key-exchange public key for the mixnode.
	pub kx_public: KxPublic,
	/// libp2p peer ID of the mixnode.
	pub peer_id: PeerId,
	/// External addresses for the mixnode, in multiaddr format, UTF-8 encoded.
	pub external_addresses: Vec<Vec<u8>>,
}

/// Error querying the runtime for a session's mixnode set.
#[derive(Decode, Encode, TypeInfo)]
pub enum MixnodesErr {
	/// Insufficient mixnodes were registered for the session.
	InsufficientRegistrations {
		/// The number of mixnodes that were registered for the session.
		num: u32,
		/// The minimum number of mixnodes that must be registered for the mixnet to operate.
		min: u32,
	},
}

impl sp_std::fmt::Display for MixnodesErr {
	fn fmt(&self, fmt: &mut sp_std::fmt::Formatter) -> sp_std::fmt::Result {
		match self {
			MixnodesErr::InsufficientRegistrations { num, min } =>
				write!(fmt, "{num} mixnode(s) registered; {min} is the minimum"),
		}
	}
}
