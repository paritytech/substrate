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
