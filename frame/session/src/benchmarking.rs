// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Benchmarks for the Session Pallet.

use super::*;

use frame_system::RawOrigin;
use sp_std::prelude::*;
use frame_benchmarking::{benchmarks, account};

use crate::Module as Session;
use frame_staking::Module as Staking;

const SEED: u32 = 0;

benchmarks! {
	_ {
		let u in 0 .. 100 => ();
	}

	set_keys {
		let u in ...;
		let user = account("user", u, SEED);
		let keys = T::Keys::default();
		let proof: Vec<u8> = vec![0,1,2,3];
	}: _(RawOrigin::Signed(user), keys, proof)

	purge_keys {
		let u in ...;
		let user = account("user", u, SEED);
		let keys = T::Keys::default();
		let proof: Vec<u8> = vec![0,1,2,3];
	}: _(RawOrigin::Signed(user))

}
