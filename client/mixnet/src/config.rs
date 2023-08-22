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

pub use mixnet::core::Config as CoreConfig;
use std::time::Duration;

/// Substrate-specific mixnet configuration.
#[derive(Clone, Debug)]
pub struct SubstrateConfig {
	/// Attempt to register the local node as a mixnode?
	pub register: bool,
	/// Maximum number of incoming mixnet connections to accept from non-mixnodes. If the local
	/// node will never be a mixnode, this can be set to 0.
	pub num_gateway_slots: u32,

	/// Number of requests to the mixnet service that can be buffered, in addition to the one per
	/// [`Api`](super::api::Api) instance. Note that this does not include requests that are being
	/// actively handled.
	pub request_buffer: usize,
	/// Used to determine the number of SURBs to include in request messages: the maximum number of
	/// SURBs needed for a single reply is multiplied by this. This should not be set to 0.
	pub surb_factor: usize,

	/// Maximum number of submit extrinsic requests waiting for their delay to elapse. When at the
	/// limit, any submit extrinsic requests that arrive will simply be dropped.
	pub extrinsic_queue_capacity: usize,
	/// Mean delay between receiving a submit extrinsic request and actually submitting the
	/// extrinsic. This should really be the same for all nodes!
	pub mean_extrinsic_delay: Duration,
	/// Maximum number of extrinsics being actively submitted. If a submit extrinsic request's
	/// delay elapses and we are already at this limit, the request will simply be dropped.
	pub max_pending_extrinsics: usize,
}

impl Default for SubstrateConfig {
	fn default() -> Self {
		Self {
			register: true,
			num_gateway_slots: 150,

			request_buffer: 4,
			surb_factor: 2,

			extrinsic_queue_capacity: 50,
			mean_extrinsic_delay: Duration::from_secs(1),
			max_pending_extrinsics: 20,
		}
	}
}

/// Mixnet configuration.
#[derive(Clone, Debug)]
pub struct Config {
	/// Core configuration.
	pub core: CoreConfig,
	/// Request manager configuration.
	pub request_manager: mixnet::request_manager::Config,
	/// Reply manager configuration.
	pub reply_manager: mixnet::reply_manager::Config,
	/// Substrate-specific configuration.
	pub substrate: SubstrateConfig,
}

impl Default for Config {
	fn default() -> Self {
		Self {
			core: Default::default(),
			request_manager: Default::default(),
			reply_manager: Default::default(),
			substrate: Default::default(),
		}
	}
}
