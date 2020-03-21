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

//! Staking pallet benchmarking.

use super::*;

use frame_system::{RawOrigin as SystemOrigin, Call as SystemCall};
use frame_benchmarking::{benchmarks_instance, account, Benchmarking, BenchmarkResults};

use crate::Module as Collective;
use frame_system::Module as System;

const SEED: u32 = 0;

benchmarks_instance! {
	_{
		// User account seed
		let u in 1 .. 1000 => ();
		let m in 1 .. 1000 => ();
	}

	set_members {
		let m in ...;

		// Construct `new_members`. It should influence timing since it will sort this vector.
		let mut new_members = vec![];
		for i in 0 .. m {
			let user = account("user", i, SEED);
			new_members.push(user);
		}

		// Construct `prime`. It shouldn't influence timing.
		let prime = Some(account("prime", 0, SEED));

	}: _(SystemOrigin::Root, new_members, prime)

	execute {
		let u in ...;

		let caller: T::AccountId = account("caller", u, SEED);
		let proposal = SystemCall::<T>::remark(Default::default());

		Collective::<T, _>::set_members(SystemOrigin::Root.into(), vec![caller.clone()], None)?;

	}: _(SystemOrigin::Signed(caller), Box::new(proposal.into()))
}
