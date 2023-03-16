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

//! Substrate chain specification API.
//!
//! The *chain spec* (short for *chain specification*) allows inspecting the content of
//! the specification of the chain that a JSON-RPC server is targeting.
//!
//! The values returned by the API are guaranteed to never change during the lifetime of the
//! JSON-RPC server.
//!
//! # Note
//!
//! Methods are prefixed by `chainSpec`.

#[cfg(test)]
mod tests;

pub mod api;
pub mod chain_spec;

pub use api::ChainSpecApiServer;
pub use chain_spec::ChainSpec;
