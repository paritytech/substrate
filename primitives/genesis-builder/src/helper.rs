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

//! Generic implementation of genesis config builder

use frame_support::traits::GenesisBuild;

pub struct GenesisBuilder<R, GC>(sp_std::marker::PhantomData<(R, GC)>);

impl<R, GC> GenesisBuilder<R, GC>
where
	GC: Default + GenesisBuild<R>,
{
	pub fn default_genesis_config_as_json() -> sp_std::vec::Vec<u8> {
		serde_json::to_string(&GC::default())
			.expect("serialization to json is expected to work. qed.")
			.into_bytes()
	}

	pub fn build_genesis_config_from_json(json: sp_std::vec::Vec<u8>) {
		let gc = serde_json::from_slice::<GC>(&json)
			.expect("provided json blob is expected to be valid. qed.");
		<GC as GenesisBuild<R>>::build(&gc);
	}
}
