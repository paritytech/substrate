// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
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
//! Used for BEEFY gadget interal error handling only

use std::fmt::Debug;

use sp_core::crypto::Public;

/// Crypto related errors
#[derive(Debug, thiserror::Error)]
pub(crate) enum Crypto<Id: Public + Debug> {
	/// Check signature error
	#[error("Message signature {0} by {1:?} is invalid.")]
	InvalidSignature(String, Id),
	/// Sign commitment error
	#[error("Failed to sign comitment using key: {0:?}. Reason: {1}")]
	CannotSign(Id, String),
}
