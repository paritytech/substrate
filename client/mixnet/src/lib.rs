// This file is part of Substrate.

// Copyright (C) 2022-2023 Parity Technologies (UK) Ltd.
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

//! Substrate mixnet service. This implements the [Substrate Mix Network
//! Specification](https://paritytech.github.io/mixnet-spec/).

#![warn(missing_docs)]
#![forbid(unsafe_code)]

mod api;
mod config;
mod error;
mod extrinsic_queue;
mod maybe_inf_delay;
mod packet_dispatcher;
mod peer_id;
mod protocol;
mod request;
mod run;
mod sync_with_runtime;

pub use self::{
	api::{Api, ApiBackend},
	config::{Config, CoreConfig, SubstrateConfig},
	error::{Error, RemoteErr},
	protocol::{peers_set_config, protocol_name},
	run::run,
};
pub use mixnet::core::{PostErr, TopologyErr};
