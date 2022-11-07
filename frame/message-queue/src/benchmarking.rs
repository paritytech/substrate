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

	// `service_queue` without any page processing or unknitting.
	service_queue_base {
		let mut meter = WeightCounter::unlimited();
	}: {
		MessageQueue::<T>::service_queue(0u32.into(), &mut meter, Weight::MAX)
	}

	// `service_page` without any message processing but with page completion.
	service_page_base {
		let origin: MessageOriginOf<T> = 0.into();
		let (page, msgs) = full_page::<T>();
		Pages::<T>::insert(&origin, 0, &page);
		let mut book_state = single_page_book::<T>();
		let mut meter = WeightCounter::unlimited();
		let limit = Weight::MAX;
	}: {
		MessageQueue::<T>::service_page(&origin, &mut book_state, &mut meter, limit)
	}

	// Worst case path of `ready_ring_unknit`.
	ready_ring_unknit {
		let origin: MessageOriginOf<T> = 0.into();
		let neighbours = Neighbours::<MessageOriginOf<T>> {
			prev: 0.into(),
			next: 1.into()
		};
		ServiceHead::<T>::put(&origin);
	}: {
		MessageQueue::<T>::ready_ring_unknit(&origin, neighbours);
	}

	// Processing a single message from a page.
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

	reap_page {
		assert!(T::MaxStale::get() >= 2, "pre-condition: MaxStale needs to be at least two");

		for i in 0..(T::MaxStale::get() + 2) {
			MessageQueue::<T>::enqueue_message(msg(&"weight=2"), 0.into());
		}
		MessageQueue::<T>::service_queues(1.into_weight());

	}: _(RawOrigin::Signed(whitelisted_caller()), 0u32.into(), 0)
	verify {
		assert_last_event::<T>(Event::PageReaped{ origin: 0.into(), index: 0 }.into());
	}

	// Create a test for each benchmark.
	impl_benchmark_test_suite!(MessageQueue, crate::mock::new_test_ext::<crate::tests::Test>(), crate::tests::Test);
}
