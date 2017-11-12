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

//! Polkadot state machine

#![warn(missing_docs)]

extern crate polkadot_primitives as primitives;

use std::fmt;

use primitives::contract::{CallData, OutData};

/// State Machine Error bound.
///
/// This should reflect WASM error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}

/// Externalities
pub trait Externalities<Executor> {
	/// Externalities error type.
	type Error: Error;
}

/// Contract code executor.
pub trait Executor: Sized {
	/// Error type for contract execution.
	type Error: Error;

	/// Execute a contract in read-only mode.
	/// The execution is not allowed to modify the state.
	fn static_call<E: Externalities<Self>>(
		&self,
		ext: &E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;

	/// Execute a contract.
	fn call<E: Externalities<Self>>(
		&self,
		ext: &mut E,
		code: &[u8],
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;
}
