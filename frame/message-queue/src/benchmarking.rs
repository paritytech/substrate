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

use super::{mock::*, Pallet as MessageQueue, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Get;
use frame_system::{Pallet as System, RawOrigin};
use sp_std::prelude::*;

static LOG_TARGET: &'static str = "runtime::message-queue::bench";

benchmarks! {
	where_clause {
		// NOTE: We need to generate multiple origins; therefore Origin must be `From<u32>`.
		where <<T as Config>::MessageProcessor as ProcessMessage>::Origin: From<u32>
	}

	// Just calling `service_queue` without any iterations happening.
	service_queue_base { }: { }

	// Just calling `service_page` without any iterations happening.
	service_page_base {	}: { }

	// Processing a single message from a page.
	//
	// The benchmarks uses a full page and skips all message except the last one,
	// although this should not make a difference.
	service_page_item {
		let (mut page, msgs) = full_page::<T>();
		// Skip all messages except the last one.
		for i in 1..msgs {
			page.skip_first(true);
		}
		assert!(page.peek_first().is_some(), "There is one message left");
		let mut weight = WeightCounter::unlimited();
		log::debug!(target: LOG_TARGET, "{} messages per page", msgs);
	}: {
		let status = MessageQueue::<T>::service_page_item(&0u32.into(), &mut page, &mut weight, Weight::MAX);
		assert_eq!(status, PageExecutionStatus::Partial);
	} verify {
		// Check fot the `Processed` event
		assert_last_event::<T>(Event::Processed {
			hash: T::Hashing::hash(&[]), origin: ((msgs - 1) as u32).into(),
			weight_used: 1.into_weight(), success: true
		}.into());
	}

	// Contains the effort for fetching and (storing or removing) a page.
	service_page_process_message { }: { }

	// Worst case for calling `bump_service_head`.
	bump_service_head { }: {}

	// Create a test for each benchmark.
	impl_benchmark_test_suite!(MessageQueue, crate::tests::new_test_ext(), crate::tests::Test);
}

fn assert_last_event<T: Config>(generic_event: <T as Config>::RuntimeEvent) {
	assert!(!System::<T>::block_number().is_zero(), "The genesis block has n o events");
	System::<T>::assert_last_event(generic_event.into());
}
