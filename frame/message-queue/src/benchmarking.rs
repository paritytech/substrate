// Copyright 2022 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

//! Benchmarking for the message queue pallet.

#![cfg(feature = "runtime-benchmarks")]

use super::{Pallet as MessageQueue, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Get;
use frame_system::RawOrigin;
use sp_std::prelude::*;

benchmarks! {
	// Just calling `service_queue` without any iterations happening.
	service_queue_base { }: { }

	// Just calling `service_page` without any iterations happening.
	service_page_base {	}: { }

	service_page_item { }: { }

	// Contains the effort for fetching and (storing or removing) a page.
	service_page_process_message { }: { }

	// Worst case for calling `bump_service_head`.
	bump_service_head { }: {}
}
