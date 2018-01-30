// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Miscellaneous small types.

/// The Ed25519 pubkey that identifies an account.
pub type AccountID = [u8; 32];

/// Virtual account ID that represents the idea of a dispatch/statement being signed by everybody
/// (who matters). Essentially this means that a majority of validators have decided it is
/// "correct".
pub const EVERYBODY: AccountID = [255u8; 32];

/// The Ed25519 pub key of an session that belongs to an authority. This is used as what the
/// external environment/consensus algorithm calls an "authority".
pub type SessionKey = AccountID;

/// Indentifier for a chain.
pub type ChainID = u64;

/// Index of a block in the chain.
pub type BlockNumber = u64;

/// Index of a transaction.
pub type TxOrder = u64;

/// A hash of some data.
pub type Hash = [u8; 32];
