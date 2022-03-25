// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Shared logic between on-chain and off-chain components used for slashing using an off-chain
//! worker.

use codec::Encode;
use sp_staking::SessionIndex;
use sp_std::prelude::*;

pub(super) const PREFIX: &[u8] = b"session_historical";
pub(super) const LAST_PRUNE: &[u8] = b"session_historical_last_prune";

/// Derive the key used to store the list of validators
pub(super) fn derive_key<P: AsRef<[u8]>>(prefix: P, session_index: SessionIndex) -> Vec<u8> {
	let prefix: &[u8] = prefix.as_ref();
	session_index.using_encoded(|encoded_session_index| {
		prefix
			.into_iter()
			.chain(b"/".into_iter())
			.chain(encoded_session_index.into_iter())
			.copied()
			.collect::<Vec<u8>>()
	})
}
