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

//! Definition of constant storage keys.

/// Prefixes account ID and stores u64 nonce.
pub const NONCE_OF: &[u8] = b"sys:non:";
/// Prefixes block number and stores hash of that block.
pub const BLOCK_HASH_AT: &[u8] = b"sys:old:";
/// Stores the temporary current transaction number.
pub const TEMP_TRANSACTION_NUMBER: &[u8] = b"temp:txcount";
