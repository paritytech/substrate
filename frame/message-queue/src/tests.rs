// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

// Tests for Multisig Pallet

#![cfg(test)]

use crate::{mock::*, *};

use frame_support::{assert_noop, assert_ok, assert_storage_noop, StorageNoopGuard};
use rand::{Rng, SeedableRng};

#[test]
fn mocked_weight_works() {
	new_test_ext::<Test>().execute_with(|| {
		assert!(<Test as Config>::WeightInfo::service_queue_base().is_zero());
	});
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_queue_base", Weight::MAX);
		assert_eq!(<Test as Config>::WeightInfo::service_queue_base(), Weight::MAX);
	});
	// The externalities reset it.
	new_test_ext::<Test>().execute_with(|| {
		assert!(<Test as Config>::WeightInfo::service_queue_base().is_zero());
	});
}

#[test]
fn enqueue_within_one_page_works() {
	new_test_ext::<Test>().execute_with(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(msg(&"a"), Here);
		MessageQueue::enqueue_message(msg(&"b"), Here);
		MessageQueue::enqueue_message(msg(&"c"), Here);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![(b"a".to_vec(), Here), (b"b".to_vec(), Here)]);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![(b"c".to_vec(), Here)]);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![]);

		MessageQueue::enqueue_messages(
			[
				BoundedSlice::truncate_from(&b"a"[..]),
				BoundedSlice::truncate_from(&b"b"[..]),
				BoundedSlice::truncate_from(&b"c"[..]),
			]
			.into_iter(),
			There,
		);

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::get(), vec![(b"a".to_vec(), There), (b"b".to_vec(), There),]);

		MessageQueue::enqueue_message(BoundedSlice::truncate_from(&b"d"[..]), Everywhere(1));

		MessagesProcessed::set(vec![]);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(b"c".to_vec(), There), (b"d".to_vec(), Everywhere(1))]
		);
	});
}

#[test]
fn queue_priority_retains() {
	new_test_ext::<Test>().execute_with(|| {
		use MessageOrigin::*;
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![]);
		MessageQueue::enqueue_message(msg(&"a"), Everywhere(1));
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![Everywhere(1)]);
		MessageQueue::enqueue_message(msg(&"b"), Everywhere(2));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2)]
		);
		MessageQueue::enqueue_message(msg(&"c"), Everywhere(3));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2), Everywhere(3)]
		);
		MessageQueue::enqueue_message(msg(&"d"), Everywhere(2));
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(1), Everywhere(2), Everywhere(3)]
		);
		// service head is 1, it will process a, leaving service head at 2. it also processes b but
		// doees not empty queue 2, so service head will end at 2.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(vmsg(&"a"), Everywhere(1)), (vmsg(&"b"), Everywhere(2)),]
		);
		assert_eq!(
			ReadyRing::<Test>::new().collect::<Vec<_>>(),
			vec![Everywhere(2), Everywhere(3)]
		);
		// service head is 2, so will process d first, then c.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![
				(vmsg(&"a"), Everywhere(1)),
				(vmsg(&"b"), Everywhere(2)),
				(vmsg(&"d"), Everywhere(2)),
				(vmsg(&"c"), Everywhere(3)),
			]
		);
		assert_eq!(ReadyRing::<Test>::new().collect::<Vec<_>>(), vec![]);
	});
}

#[test]
fn queue_priority_reset_once_serviced() {
	new_test_ext::<Test>().execute_with(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(msg(&"a"), Everywhere(1));
		MessageQueue::enqueue_message(msg(&"b"), Everywhere(2));
		MessageQueue::enqueue_message(msg(&"c"), Everywhere(3));
		// service head is 1, it will process a, leaving service head at 2. it also processes b and
		// empties queue 2, so service head will end at 3.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		MessageQueue::enqueue_message(msg(&"d"), Everywhere(2));
		// service head is 3, so will process c first, then d.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());

		assert_eq!(
			MessagesProcessed::get(),
			vec![
				(vmsg(&"a"), Everywhere(1)),
				(vmsg(&"b"), Everywhere(2)),
				(vmsg(&"c"), Everywhere(3)),
				(vmsg(&"d"), Everywhere(2)),
			]
		);
	});
}

#[test]
fn reap_page_permanent_overweight_works() {
	assert!(MaxStale::get() >= 2, "pre-condition unmet");
	new_test_ext::<Test>().execute_with(|| {
		use MessageOrigin::*;
		// Create pages with messages with a weight of two.
		for _ in 0..(MaxStale::get() * MaxStale::get()) {
			MessageQueue::enqueue_message(msg(&"weight=2"), Here);
		}

		// … but only allow the processing to take at most weight 1.
		MessageQueue::service_queues(1.into_weight());

		// We can now reap the first one since they are permanently overweight and over the MaxStale
		// limit.
		assert_ok!(MessageQueue::do_reap_page(&Here, 0));
		// Cannot reap again.
		assert_noop!(MessageQueue::do_reap_page(&Here, 0), Error::<Test>::NoPage);
	});
}

#[test]
fn reaping_overweight_fails_properly() {
	new_test_ext::<Test>().execute_with(|| {
		use MessageOrigin::*;
		// page 0
		MessageQueue::enqueue_message(msg(&"weight=4"), Here);
		MessageQueue::enqueue_message(msg(&"a"), Here);
		// page 1
		MessageQueue::enqueue_message(msg(&"weight=4"), Here);
		MessageQueue::enqueue_message(msg(&"b"), Here);
		// page 2
		MessageQueue::enqueue_message(msg(&"weight=4"), Here);
		MessageQueue::enqueue_message(msg(&"c"), Here);
		// page 3
		MessageQueue::enqueue_message(msg(&"bigbig 1"), Here);
		// page 4
		MessageQueue::enqueue_message(msg(&"bigbig 2"), Here);
		// page 5
		MessageQueue::enqueue_message(msg(&"bigbig 3"), Here);

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg(&"a"), Here), (vmsg(&"b"), Here)]);
		// 2 stale now.

		// Not reapable yet, because we haven't hit the stale limit.
		assert_noop!(MessageQueue::do_reap_page(&Here, 0), Error::<Test>::NotReapable);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg(&"c"), Here)]);
		// 3 stale now: can take something 4 pages in history.

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg(&"bigbig 1"), Here)]);

		// Not reapable yet, because we haven't hit the stale limit.
		assert_noop!(MessageQueue::do_reap_page(&Here, 0), Error::<Test>::NotReapable);
		assert_noop!(MessageQueue::do_reap_page(&Here, 1), Error::<Test>::NotReapable);
		assert_noop!(MessageQueue::do_reap_page(&Here, 2), Error::<Test>::NotReapable);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg(&"bigbig 2"), Here)]);

		// First is now reapable as it is too far behind the first ready page (5).
		assert_ok!(MessageQueue::do_reap_page(&Here, 0));
		// Others not reapable yet, because we haven't hit the stale limit.
		assert_noop!(MessageQueue::do_reap_page(&Here, 1), Error::<Test>::NotReapable);
		assert_noop!(MessageQueue::do_reap_page(&Here, 2), Error::<Test>::NotReapable);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg(&"bigbig 3"), Here)]);

		assert_noop!(MessageQueue::do_reap_page(&Here, 0), Error::<Test>::NoPage);
		// Still not reapable, since the number of stale pages is only 2.
		assert_noop!(MessageQueue::do_reap_page(&Here, 1), Error::<Test>::NotReapable);
		assert_noop!(MessageQueue::do_reap_page(&Here, 2), Error::<Test>::NotReapable);
	});
}

#[test]
fn service_queue_bails() {
	// Not enough weight for `service_queue_base`.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_queue_base", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		assert_storage_noop!(MessageQueue::service_queue(0u32.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed.is_zero());
	});
	// Not enough weight for `ready_ring_unknit`.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("ready_ring_unknit", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		assert_storage_noop!(MessageQueue::service_queue(0u32.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed.is_zero());
	});
	// Not enough weight for `service_queue_base` and `ready_ring_unknit`.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_queue_base", 2.into_weight());
		set_weight("ready_ring_unknit", 2.into_weight());

		let mut meter = WeightMeter::from_limit(3.into_weight());
		assert_storage_noop!(MessageQueue::service_queue(0.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed.is_zero());
	});
}

#[test]
fn service_page_works() {
	use super::integration_test::Test;
	use MessageOrigin::*;
	use PageExecutionStatus::*; // Run with larger page size.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_page_base_completion", 2.into_weight());
		set_weight("service_page_item", 3.into_weight());

		let (page, mut msgs) = full_page::<Test>();
		assert!(msgs >= 10, "pre-condition: need at least 10 msgs per page");
		let mut book = book_for::<Test>(&page);
		Pages::<Test>::insert(&Here, 0, page);

		// Call it a few times each with a random weight limit.
		let mut rng = rand::rngs::StdRng::seed_from_u64(42);
		while msgs > 0 {
			let process = rng.gen_range(0..=msgs);
			msgs -= process;

			//  Enough weight to process `process` messages.
			let mut meter = WeightMeter::from_limit(((2 + (3 + 1) * process) as u64).into_weight());
			System::reset_events();
			let (processed, status) =
				crate::Pallet::<Test>::service_page(&Here, &mut book, &mut meter, Weight::MAX);
			assert_eq!(processed as usize, process);
			assert_eq!(NumMessagesProcessed::take(), process);
			assert_eq!(System::events().len(), process);
			if msgs == 0 {
				assert_eq!(status, NoMore);
			} else {
				assert_eq!(status, Bailed);
			}
		}
		assert!(!Pages::<Test>::contains_key(&Here, 0), "The page got removed");
	});
}

// `service_page` does nothing when called with an insufficient weight limit.
#[test]
fn service_page_bails() {
	// Not enough weight for `service_page_base_completion`.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_page_base_completion", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		let (page, _) = full_page::<Test>();
		let mut book = book_for::<Test>(&page);
		Pages::<Test>::insert(MessageOrigin::Here, 0, page);

		assert_storage_noop!(MessageQueue::service_page(
			&MessageOrigin::Here,
			&mut book,
			&mut meter,
			Weight::MAX
		));
		assert!(meter.consumed.is_zero());
	});
	// Not enough weight for `service_page_base_no_completion`.
	new_test_ext::<Test>().execute_with(|| {
		set_weight("service_page_base_no_completion", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		let (page, _) = full_page::<Test>();
		let mut book = book_for::<Test>(&page);
		Pages::<Test>::insert(MessageOrigin::Here, 0, page);

		assert_storage_noop!(MessageQueue::service_page(
			&MessageOrigin::Here,
			&mut book,
			&mut meter,
			Weight::MAX
		));
		assert!(meter.consumed.is_zero());
	});
}

#[test]
fn service_page_item_bails() {
	new_test_ext::<Test>().execute_with(|| {
		let _guard = StorageNoopGuard::default();
		let (mut page, _) = full_page::<Test>();
		let mut weight = WeightMeter::from_limit(10.into_weight());
		let overweight_limit = 10.into_weight();
		set_weight("service_page_item", 11.into_weight());

		assert_eq!(
			MessageQueue::service_page_item(
				&MessageOrigin::Here,
				0,
				&mut book_for::<Test>(&page),
				&mut page,
				&mut weight,
				overweight_limit,
			),
			PageExecutionStatus::Bailed
		);
	});
}

/// `bump_service_head` does nothing when called with an insufficient weight limit.
#[test]
fn bump_service_head_bails() {
	new_test_ext::<Test>().execute_with(|| {
		set_weight("bump_service_head", 2.into_weight());
		setup_bump_service_head::<Test>(0.into(), 10.into());

		let _guard = StorageNoopGuard::default();
		let mut meter = WeightMeter::from_limit(1.into_weight());
		assert!(MessageQueue::bump_service_head(&mut meter).is_none());
		assert_eq!(meter.consumed, 0.into_weight());
	});
}

#[test]
fn bump_service_head_works() {
	new_test_ext::<Test>().execute_with(|| {
		set_weight("bump_service_head", 2.into_weight());
		let mut meter = WeightMeter::max_limit();

		assert_eq!(MessageQueue::bump_service_head(&mut meter), None, "Cannot bump");
		assert_eq!(meter.consumed, 2.into_weight());

		setup_bump_service_head::<Test>(0.into(), 1.into());

		assert_eq!(MessageQueue::bump_service_head(&mut meter), Some(0.into()));
		assert_eq!(ServiceHead::<Test>::get().unwrap(), 1.into(), "Bumped the head");
		assert_eq!(meter.consumed, 4.into_weight());

		assert_eq!(MessageQueue::bump_service_head(&mut meter), None, "Cannot bump");
		assert_eq!(meter.consumed, 6.into_weight());
	});
}

#[test]
fn service_page_item_consumes_correct_weight() {
	new_test_ext::<Test>().execute_with(|| {
		let mut page = page::<Test>(b"weight=3");
		let mut weight = WeightMeter::from_limit(10.into_weight());
		let overweight_limit = 0.into_weight();
		set_weight("service_page_item", 2.into_weight());

		assert_eq!(
			MessageQueue::service_page_item(
				&MessageOrigin::Here,
				0,
				&mut book_for::<Test>(&page),
				&mut page,
				&mut weight,
				overweight_limit
			),
			PageExecutionStatus::Partial
		);
		assert_eq!(weight.consumed, 5.into_weight());
	});
}

/// `service_page_item` skips a permanently `Overweight` message and marks it as `unprocessed`.
#[test]
fn service_page_item_skips_perm_overweight_message() {
	new_test_ext::<Test>().execute_with(|| {
		let mut page = page::<Test>(b"TooMuch");
		let mut weight = WeightMeter::from_limit(2.into_weight());
		let overweight_limit = 0.into_weight();
		set_weight("service_page_item", 2.into_weight());

		assert_eq!(
			crate::Pallet::<Test>::service_page_item(
				&MessageOrigin::Here,
				0,
				&mut book_for::<Test>(&page),
				&mut page,
				&mut weight,
				overweight_limit
			),
			PageExecutionStatus::Partial
		);
		assert_eq!(weight.consumed, 2.into_weight());
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				hash: <Test as frame_system::Config>::Hashing::hash(b"TooMuch"),
				origin: MessageOrigin::Here,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);

		// Check that the message was skipped.
		let (pos, processed, payload) = page.peek_index(0).unwrap();
		assert_eq!(pos, 0);
		assert_eq!(processed, false);
		assert_eq!(payload, b"TooMuch".encode());
	});
}

#[test]
fn peek_index_works() {
	use super::integration_test::Test; // Run with larger page size.
	new_test_ext::<Test>().execute_with(|| {
		// Fill a page with messages.
		let (mut page, msgs) = full_page::<Test>();
		let msg_enc_len = ItemHeader::<<Test as Config>::Size>::max_encoded_len() + 4;

		for i in 0..msgs {
			// Skip all even messages.
			page.skip_first(i % 2 == 0);
			// Peek each message and check that it is correct.
			let (pos, processed, payload) = page.peek_index(i).unwrap();
			assert_eq!(pos, msg_enc_len * i);
			assert_eq!(processed, i % 2 == 0);
			// `full_page` uses the index as payload.
			assert_eq!(payload, (i as u32).encode());
		}
	});
}

#[test]
fn peek_first_works() {
	use super::integration_test::Test; // Run with larger page size.
	new_test_ext::<Test>().execute_with(|| {
		// Fill a page with messages.
		let (mut page, msgs) = full_page::<Test>();

		for i in 0..msgs {
			let msg = page.peek_first().unwrap();
			// `full_page` uses the index as payload.
			assert_eq!(msg.deref(), (i as u32).encode());
			page.skip_first(i % 2 == 0); // True of False should not matter here.
		}
		assert!(page.peek_first().is_none(), "Page must be at the end");
	});
}

#[test]
fn note_processed_at_pos_works() {
	use super::integration_test::Test; // Run with larger page size.
	new_test_ext::<Test>().execute_with(|| {
		let (mut page, msgs) = full_page::<Test>();

		for i in 0..msgs {
			let (pos, processed, _) = page.peek_index(i).unwrap();
			assert_eq!(processed, false);
			assert_eq!(page.remaining as usize, msgs - i);

			page.note_processed_at_pos(pos);

			let (_, processed, _) = page.peek_index(i).unwrap();
			assert_eq!(processed, true);
			assert_eq!(page.remaining as usize, msgs - i - 1);
		}
	});
}

#[test]
fn is_complete_works() {
	use super::integration_test::Test; // Run with larger page size.
	new_test_ext::<Test>().execute_with(|| {
		let (mut page, msgs) = full_page::<Test>();
		assert!(msgs > 3, "Boring");
		let msg_enc_len = ItemHeader::<<Test as Config>::Size>::max_encoded_len() + 4;

		assert!(!page.is_complete());
		for i in 0..msgs {
			if i % 2 == 0 {
				page.skip_first(false);
			} else {
				page.note_processed_at_pos(msg_enc_len * i);
			}
		}
		// Not complete since `skip_first` was called with `false`.
		assert!(!page.is_complete());
		for i in 0..msgs {
			if i % 2 == 0 {
				assert!(!page.is_complete());
				let (pos, _, _) = page.peek_index(i).unwrap();
				page.note_processed_at_pos(pos);
			}
		}
		assert!(page.is_complete());
		assert_eq!(page.remaining_size, 0);
		// Each message is marked as processed.
		for i in 0..msgs {
			let (_, processed, _) = page.peek_index(i).unwrap();
			assert_eq!(processed, true);
		}
	});
}

#[test]
fn page_from_message_basic_works() {
	assert!(MaxOriginLenOf::<Test>::get() >= 3, "pre-condition unmet");
	assert!(MaxMessageLenOf::<Test>::get() >= 3, "pre-condition unmet");

#[test]
fn page_try_append_message_max_msg_len_works_works() {
	use super::integration_test::Test; // Run with larger page size.

	// We start off with an empty page.
	let mut page = PageOf::<Test>::default();
	// … and append a message with maximum possible length.
	let mut msg = vec![123u8; MaxMessageLenOf::<Test>::get() as usize];
	// … which works.
	page.try_append_message::<Test>(BoundedSlice::defensive_truncate_from(&msg))
		.unwrap();
	// Now we cannot append *anything* since the heap is full.
	page.try_append_message::<Test>(BoundedSlice::defensive_truncate_from(&[]))
		.unwrap_err();
	assert_eq!(page.heap.len(), <Test as Config>::HeapSize::get() as usize);
}

	let _page = PageOf::<Test>::from_message::<Test>(BoundedSlice::defensive_truncate_from(b"MSG"));
}

// `Page::from_message` does not panic when called with the maximum message and origin lengths.
#[test]
fn page_from_message_max_len_works() {
	let max_msg_len: usize = MaxMessageLenOf::<Test>::get() as usize;

	let page = PageOf::<Test>::from_message::<Test>(vec![1; max_msg_len][..].try_into().unwrap());

	assert_eq!(page.remaining, 1);
}

#[test]
fn sweep_queue_works() {
	new_test_ext::<Test>().execute_with(|| {
		let origin = MessageOrigin::Here;
		let (page, _) = full_page::<Test>();
		let book = book_for::<Test>(&page);
		assert!(book.begin != book.end, "pre-condition: the book is not empty");
		Pages::<Test>::insert(&origin, &0, &page);
		BookStateFor::<Test>::insert(&origin, &book);

		MessageQueue::sweep_queue(origin);
		// The book still exits, but has updated begin and end.
		let book = BookStateFor::<Test>::get(&origin);
		assert_eq!(book.begin, book.end, "Begin and end are now the same");
		assert!(Pages::<Test>::contains_key(&origin, &0), "Page was not swept");
	})
}

#[test]
fn footprint_works() {
	new_test_ext::<Test>().execute_with(|| {
		let origin = MessageOrigin::Here;
		let (page, msgs) = full_page::<Test>();
		let book = book_for::<Test>(&page);
		BookStateFor::<Test>::insert(&origin, &book);

		let info = MessageQueue::footprint(origin);
		assert_eq!(info.count as usize, msgs);
		assert_eq!(info.size, page.remaining_size);
	})
}

#[test]
fn footprint_default_works() {
	new_test_ext::<Test>().execute_with(|| {
		let origin = MessageOrigin::Here;
		assert_eq!(MessageQueue::footprint(origin), Default::default());
	})
}

#[test]
fn execute_overweight_works() {
	new_test_ext::<Test>().execute_with(|| {
		set_weight("bump_service_head", 1.into_weight());
		set_weight("service_queue_base", 1.into_weight());
		set_weight("service_page_base_completion", 1.into_weight());

		// Enqueue a message
		let origin = MessageOrigin::Here;
		MessageQueue::enqueue_message(msg(&"weight=6"), origin);
		// Load the current book
		let book = BookStateFor::<Test>::get(&origin);
		assert_eq!(book.message_count, 1);

		// Mark the message as permanently overweight.
		assert_eq!(MessageQueue::service_queues(4.into_weight()), 4.into_weight());
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				hash: <Test as frame_system::Config>::Hashing::hash(b"weight=6"),
				origin: MessageOrigin::Here,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);
		// Now try to execute it.
		let consumed = MessageQueue::do_execute_overweight(origin, 0, 0, 7.into_weight()).unwrap();
		assert_eq!(consumed, 6.into_weight());
		// There is no message left in the book.
		let book = BookStateFor::<Test>::get(&origin);
		assert_eq!(book.message_count, 0);
		// Doing it again will error.
		let consumed =
			MessageQueue::do_execute_overweight(origin, 0, 0, 60.into_weight()).unwrap_err();
	});
}
