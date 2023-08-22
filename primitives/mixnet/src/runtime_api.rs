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

//! Runtime API for querying mixnet configuration and registering mixnodes.

use super::types::{Mixnode, MixnodesErr, SessionIndex, SessionStatus};
use sp_std::vec::Vec;

sp_api::decl_runtime_apis! {
	/// API to query the mixnet session status and mixnode sets, and to register mixnodes.
	pub trait MixnetApi {
		/// Get the index and phase of the current session.
		fn session_status() -> SessionStatus;

		/// Get the mixnode set for the previous session.
		fn prev_mixnodes() -> Result<Vec<Mixnode>, MixnodesErr>;

		/// Get the mixnode set for the current session.
		fn current_mixnodes() -> Result<Vec<Mixnode>, MixnodesErr>;

		/// Try to register a mixnode for the next session. Returns `true` if a registration
		/// extrinsic is submitted. `session_index` should match `session_status().current_index`;
		/// if it does not, `false` is returned immediately. This should be called every block
		/// during the session, except, after `true` is returned, this should not be called for a
		/// few blocks, to give the submitted extrinsic a chance to get included.
		fn maybe_register(session_index: SessionIndex, mixnode: Mixnode) -> bool;
	}
}
