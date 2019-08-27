// Copyright 2018-2019 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Runtime difficulty adjustment and PoW algorithms.
//!
//! This crate contains several proof of work algorithms defined in Substrate
//! runtime. `diffs`, which contains difficulty adjustment algorithms. And `algos`,
//! which contains mining algorithms.
//!
//! Difficulty adjustment algorithms are usually defined as a SRML module because
//! it requires access to storage. To use them, implement the trait and include it
//! in your runtime. After that, make `PowApi::difficulty` points to the module's
//! `target_difficulty` function.
//!
//! Mining algorithms are usually pure functions. To use them, simply point
//! `PowApi::verify` and `PowApi::mine` to the module's `verify` and `mine` functions.

#![recursion_limit="128"]
#![cfg_attr(not(feature = "std"), no_std)]

pub mod diffs;
pub mod algos;

use core::marker::PhantomData;
use codec::Codec;
use pow_primitives::POW_ENGINE_ID;
use srml_support::ConsensusEngineId;

/// Find author routine for PoW engine.
pub struct FindAuthor<V: Codec>(PhantomData<V>);

impl<V: Codec> srml_support::traits::FindAuthor<V> for FindAuthor<V> {
	fn find_author<'a, I>(digests: I) -> Option<V> where
		I: 'a + IntoIterator<Item=(ConsensusEngineId, &'a [u8])>
	{
		for (engine_id, mut value) in digests {
			if engine_id == POW_ENGINE_ID {
				return V::decode(&mut value).ok()
			}
		}

		None
	}
}
