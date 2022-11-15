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

use super::{mock_helpers::*, Pallet as MessageQueue, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Get;
use frame_system::{Pallet as System, RawOrigin};
use sp_std::prelude::*;

benchmarks! {
	where_clause {
		where
			// NOTE: We need to generate multiple origins, therefore Origin is `From<u32>`.
			<<T as Config>::MessageProcessor as ProcessMessage>::Origin: From<u32>,
			<T as Config>::Size: From<u32>,
	}

	// `service_queue` without any page processing or unknitting.
	service_queue_base {
		let mut meter = WeightCounter::unlimited();
	}: {
		MessageQueue::<T>::service_queue(0u32.into(), &mut meter, Weight::MAX)
	}

	// `service_page` without any message processing but with page completion.
	service_page_base_completion {
		let origin: MessageOriginOf<T> = 0.into();
		let page = PageOf::<T>::default();
		Pages::<T>::insert(&origin, 0, &page);
		let mut book_state = single_page_book::<T>();
		let mut meter = WeightCounter::unlimited();
		let limit = Weight::MAX;
	}: {
		MessageQueue::<T>::service_page(&origin, &mut book_state, &mut meter, limit)
	}

	// `service_page` without any message processing and without page completion.
	service_page_base_no_completion {
		let origin: MessageOriginOf<T> = 0.into();
		let mut page = PageOf::<T>::default();
		// Mock the storage such that `is_complete` returns `false` but `peek_first` returns `None`.
		page.first = 1.into();
		page.remaining = 1.into();
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
		let msg = vec![1u8; MaxMessageLenOf::<T>::get() as usize];
		let mut page = page::<T>(&msg.clone());
		let mut book = book_for::<T>(&page);
		assert!(page.peek_first().is_some(), "There is one message");
		let mut weight = WeightCounter::unlimited();
	}: {
		let status = MessageQueue::<T>::service_page_item(&0u32.into(), 0, &mut book, &mut page, &mut weight, Weight::MAX);
		assert_eq!(status, PageExecutionStatus::Partial);
	} verify {
		// Check that it was processed.
		assert_last_event::<T>(Event::Processed {
			hash: T::Hashing::hash(&msg), origin: 0.into(),
			weight_used: 1.into_weight(), success: true
		}.into());
		let (_, processed, _) = page.peek_index(0).unwrap();
		assert!(processed);
		assert_eq!(book.message_count, 0);
	}

	// Worst case for calling `bump_service_head`.
	bump_service_head {
		setup_bump_service_head::<T>(0.into(), 10.into());
		let mut weight = WeightCounter::unlimited();
	}: {
		MessageQueue::<T>::bump_service_head(&mut weight);
	} verify {
		assert_eq!(ServiceHead::<T>::get().unwrap(), 10u32.into());
	}

	reap_page {
		// Mock the storage to get a *cullable* but not *reapable* page.
		let origin: MessageOriginOf<T> = 0.into();
		let mut book = single_page_book::<T>();
		let (page, msgs) = full_page::<T>();

		for p in 0 .. T::MaxStale::get() * T::MaxStale::get() {
			if p == 0 {
				Pages::<T>::insert(&origin, p, &page);
			}
			book.end += 1;
			book.count += 1;
			book.message_count += msgs as u32;
			book.size += page.remaining_size.into();
		}
		book.begin = book.end - T::MaxStale::get();
		BookStateFor::<T>::insert(&origin, &book);
		assert!(Pages::<T>::contains_key(&origin, 0));

	}: _(RawOrigin::Signed(whitelisted_caller()), 0u32.into(), 0)
	verify {
		assert_last_event::<T>(Event::PageReaped{ origin: 0.into(), index: 0 }.into());
		assert!(!Pages::<T>::contains_key(&origin, 0));
	}

	execute_overweight {
		// Mock the storage
		let origin: MessageOriginOf<T> = 0.into();
		let (mut page, msgs) = full_page::<T>();
		page.skip_first(false); // One skipped un-processed overweight message.
		let book = book_for::<T>(&page);
		Pages::<T>::insert(&origin, 0, &page);
		BookStateFor::<T>::insert(&origin, &book);

	}: _(RawOrigin::Signed(whitelisted_caller()), 0u32.into(), 0u32, 0u32.into(), Weight::MAX)
	verify {
		assert_last_event::<T>(Event::Processed {
			hash: T::Hashing::hash(&0u32.encode()), origin: 0.into(),
			weight_used: Weight::from_parts(1, 1), success: true
		}.into());
	}

	impl_benchmark_test_suite!(MessageQueue, crate::mock::new_test_ext::<crate::integration_test::Test>(), crate::integration_test::Test);
}
