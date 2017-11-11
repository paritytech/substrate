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

//! Temporary crate for contracts implementations.
//!
//! This will be replaced with WASM contracts stored on-chain.

#![warn(missing_docs)]

extern crate polkadot_primitives as primitives;
extern crate polkadot_serializer as serializer;
extern crate serde;

#[macro_use]
extern crate error_chain;

pub mod rust;

use primitives::contract::{CallData, OutData};

#[derive(Debug, PartialEq, Eq)]
pub struct ContractCode<'a>(&'a [u8]);

pub trait Externalities {}

pub trait Executor {
	type Error;

	fn static_call<E: Externalities>(
		&self,
		ext: &E,
		code: ContractCode,
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;

	fn call<E: Externalities>(
		&self,
		ext: &mut E,
		code: ContractCode,
		method: &str,
		data: &CallData,
	) -> Result<OutData, Self::Error>;
}
