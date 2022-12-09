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
#![allow(unused_assignments)] // Needed for `ready_ring_knit`.

use super::{mock_helpers::*, Pallet as MessageQueue, *};

use frame_benchmarking::{benchmarks, whitelisted_caller};
use frame_support::traits::Get;
use frame_system::RawOrigin;
use sp_std::prelude::*;

benchmarks! {
	where_clause {
		where
			// NOTE: We need to generate multiple origins, therefore Origin is `From<u32>`. The
			// `PartialEq` is for asserting the outcome of the ring (un)knitting and *could* be
			// removed if really necessary.
			<<T as Config>::MessageProcessor as ProcessMessage>::Origin: From<u32> + PartialEq,
			<T as Config>::Size: From<u32>,
	}

	// Worst case path of `ready_ring_knit`.
	ready_ring_knit {
		let mid: MessageOriginOf::<T> = 1.into();
		build_ring::<T>(&[0.into(), mid.clone(), 2.into()]);
		unknit::<T>(&mid);
		assert_ring::<T>(&[0.into(), 2.into()]);
		let mut neighbours = None;
	}: {
		neighbours = MessageQueue::<T>::ready_ring_knit(&mid).ok();
	} verify {
		// The neighbours needs to be modified manually.
		BookStateFor::<T>::mutate(&mid, |b| { b.ready_neighbours = neighbours });
		assert_ring::<T>(&[0.into(), 2.into(), mid]);
	}

	// Worst case path of `ready_ring_unknit`.
	ready_ring_unknit {
		build_ring::<T>(&[0.into(), 1.into(), 2.into()]);
		assert_ring::<T>(&[0.into(), 1.into(), 2.into()]);
		let o: MessageOriginOf::<T> = 0.into();
		let neighbours = BookStateFor::<T>::get(&o).ready_neighbours.unwrap();
	}: {
		MessageQueue::<T>::ready_ring_unknit(&o, neighbours);
	} verify {
		assert_ring::<T>(&[1.into(), 2.into()]);
	}

	// `service_queues` without any queue processing.
	service_queue_base {
	}: {
		MessageQueue::<T>::service_queue(0.into(), &mut WeightMeter::max_limit(), Weight::MAX)
	}

	// `service_page` without any message processing but with page completion.
	service_page_base_completion {
		let origin: MessageOriginOf<T> = 0.into();
		let page = PageOf::<T>::default();
		Pages::<T>::insert(&origin, 0, &page);
		let mut book_state = single_page_book::<T>();
		let mut meter = WeightMeter::max_limit();
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
		let mut meter = WeightMeter::max_limit();
		let limit = Weight::MAX;
	}: {
		MessageQueue::<T>::service_page(&origin, &mut book_state, &mut meter, limit)
	}

	// Processing a single message from a page.
	service_page_item {
		let msg = vec![1u8; MaxMessageLenOf::<T>::get() as usize];
		let mut page = page::<T>(&msg.clone());
		let mut book = book_for::<T>(&page);
		assert!(page.peek_first().is_some(), "There is one message");
		let mut weight = WeightMeter::max_limit();
	}: {
		let status = MessageQueue::<T>::service_page_item(&0u32.into(), 0, &mut book, &mut page, &mut weight, Weight::MAX);
		assert_eq!(status, ItemExecutionStatus::Executed(true));
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
		let mut weight = WeightMeter::max_limit();
	}: {
		MessageQueue::<T>::bump_service_head(&mut weight);
	} verify {
		assert_eq!(ServiceHead::<T>::get().unwrap(), 10u32.into());
		assert_eq!(weight.consumed, T::WeightInfo::bump_service_head());
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
			book.message_count += msgs as u64;
			book.size += page.remaining_size.into() as u64;
		}
		book.begin = book.end - T::MaxStale::get();
		BookStateFor::<T>::insert(&origin, &book);
		assert!(Pages::<T>::contains_key(&origin, 0));

	}: _(RawOrigin::Signed(whitelisted_caller()), 0u32.into(), 0)
	verify {
		assert_last_event::<T>(Event::PageReaped{ origin: 0.into(), index: 0 }.into());
		assert!(!Pages::<T>::contains_key(&origin, 0));
	}

	// Worst case for `execute_overweight` where the page is removed as completed.
	//
	// The worst case occurs when executing the last message in a page of which all are skipped since it is using `peek_index` which has linear complexities.
	execute_overweight_page_removed {
		let origin: MessageOriginOf<T> = 0.into();
		let (mut page, msgs) = full_page::<T>();
		// Skip all messages.
		for _ in 1..msgs {
			page.skip_first(true);
		}
		page.skip_first(false);
		let book = book_for::<T>(&page);
		Pages::<T>::insert(&origin, 0, &page);
		BookStateFor::<T>::insert(&origin, &book);
	}: {
		MessageQueue::<T>::execute_overweight(RawOrigin::Signed(whitelisted_caller()).into(), 0u32.into(), 0u32, ((msgs - 1) as u32).into(), Weight::MAX).unwrap()
	}
	verify {
		assert_last_event::<T>(Event::Processed {
			hash: T::Hashing::hash(&((msgs - 1) as u32).encode()), origin: 0.into(),
			weight_used: Weight::from_parts(1, 1), success: true
		}.into());
		assert!(!Pages::<T>::contains_key(&origin, 0), "Page must be removed");
	}

	// Worst case for `execute_overweight` where the page is updated.
	execute_overweight_page_updated {
		let origin: MessageOriginOf<T> = 0.into();
		let (mut page, msgs) = full_page::<T>();
		// Skip all messages.
		for _ in 0..msgs {
			page.skip_first(false);
		}
		let book = book_for::<T>(&page);
		Pages::<T>::insert(&origin, 0, &page);
		BookStateFor::<T>::insert(&origin, &book);
	}: {
		MessageQueue::<T>::execute_overweight(RawOrigin::Signed(whitelisted_caller()).into(), 0u32.into(), 0u32, ((msgs - 1) as u32).into(), Weight::MAX).unwrap()
	}
	verify {
		assert_last_event::<T>(Event::Processed {
			hash: T::Hashing::hash(&((msgs - 1) as u32).encode()), origin: 0.into(),
			weight_used: Weight::from_parts(1, 1), success: true
		}.into());
		assert!(Pages::<T>::contains_key(&origin, 0), "Page must be updated");
	}

	impl_benchmark_test_suite!(MessageQueue, crate::mock::new_test_ext::<crate::integration_test::Test>(), crate::integration_test::Test);
}
