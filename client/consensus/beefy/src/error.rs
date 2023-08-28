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

//! BEEFY gadget specific errors
//!
//! Used for BEEFY gadget internal error handling only

use std::fmt::Debug;

#[derive(Debug, thiserror::Error)]
pub enum Error {
	#[error("Backend: {0}")]
	Backend(String),
	#[error("Keystore error: {0}")]
	Keystore(String),
	#[error("Runtime api error: {0}")]
	RuntimeApi(sp_api::ApiError),
	#[error("Signature error: {0}")]
	Signature(String),
	#[error("Session uninitialized")]
	UninitSession,
	#[error("pallet-beefy was reset")]
	ConsensusReset,
	#[error("Block import stream terminated")]
	BlockImportStreamTerminated,
	#[error("Gossip Engine terminated")]
	GossipEngineTerminated,
	#[error("Finality proofs gossiping stream terminated")]
	FinalityProofGossipStreamTerminated,
	#[error("Finality stream terminated")]
	FinalityStreamTerminated,
	#[error("Votes gossiping stream terminated")]
	VotesGossipStreamTerminated,
}

#[cfg(test)]
impl PartialEq for Error {
	fn eq(&self, other: &Self) -> bool {
		match (self, other) {
			(Error::Backend(s1), Error::Backend(s2)) => s1 == s2,
			(Error::Keystore(s1), Error::Keystore(s2)) => s1 == s2,
			(Error::RuntimeApi(_), Error::RuntimeApi(_)) => true,
			(Error::Signature(s1), Error::Signature(s2)) => s1 == s2,
			(Error::UninitSession, Error::UninitSession) => true,
			(Error::ConsensusReset, Error::ConsensusReset) => true,
			_ => false,
		}
	}
}
