// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Tests for Message Queue Pallet.

#![cfg(test)]

use crate::{mock::*, *};

use frame_support::{assert_noop, assert_ok, assert_storage_noop, StorageNoopGuard};
use rand::{rngs::StdRng, Rng, SeedableRng};
use sp_core::blake2_256;

#[test]
fn mocked_weight_works() {
	build_and_execute::<Test>(|| {
		assert!(<Test as Config>::WeightInfo::service_queue_base().is_zero());
	});
	build_and_execute::<Test>(|| {
		set_weight("service_queue_base", Weight::MAX);
		assert_eq!(<Test as Config>::WeightInfo::service_queue_base(), Weight::MAX);
	});
	// The externalities reset it.
	build_and_execute::<Test>(|| {
		assert!(<Test as Config>::WeightInfo::service_queue_base().is_zero());
	});
}

#[test]
fn enqueue_within_one_page_works() {
	build_and_execute::<Test>(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(msg("a"), Here);
		MessageQueue::enqueue_message(msg("b"), Here);
		MessageQueue::enqueue_message(msg("c"), Here);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(b"a".to_vec(), Here), (b"b".to_vec(), Here)]);

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(b"c".to_vec(), Here)]);

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert!(MessagesProcessed::get().is_empty());

		MessageQueue::enqueue_messages([msg("a"), msg("b"), msg("c")].into_iter(), There);

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::take(),
			vec![(b"a".to_vec(), There), (b"b".to_vec(), There),]
		);

		MessageQueue::enqueue_message(msg("d"), Everywhere(1));

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 0.into_weight());
		assert_eq!(
			MessagesProcessed::take(),
			vec![(b"c".to_vec(), There), (b"d".to_vec(), Everywhere(1))]
		);
	});
}

#[test]
fn queue_priority_retains() {
	build_and_execute::<Test>(|| {
		use MessageOrigin::*;
		assert_ring(&[]);
		MessageQueue::enqueue_message(msg("a"), Everywhere(1));
		assert_ring(&[Everywhere(1)]);
		MessageQueue::enqueue_message(msg("b"), Everywhere(2));
		assert_ring(&[Everywhere(1), Everywhere(2)]);
		MessageQueue::enqueue_message(msg("c"), Everywhere(3));
		assert_ring(&[Everywhere(1), Everywhere(2), Everywhere(3)]);
		MessageQueue::enqueue_message(msg("d"), Everywhere(2));
		assert_ring(&[Everywhere(1), Everywhere(2), Everywhere(3)]);
		// service head is 1, it will process a, leaving service head at 2. it also processes b but
		// doees not empty queue 2, so service head will end at 2.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::take(),
			vec![(vmsg("a"), Everywhere(1)), (vmsg("b"), Everywhere(2)),]
		);
		assert_ring(&[Everywhere(2), Everywhere(3)]);
		// service head is 2, so will process d first, then c.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(
			MessagesProcessed::get(),
			vec![(vmsg("d"), Everywhere(2)), (vmsg("c"), Everywhere(3)),]
		);
		assert_ring(&[]);
	});
}

#[test]
fn queue_priority_reset_once_serviced() {
	build_and_execute::<Test>(|| {
		use MessageOrigin::*;
		MessageQueue::enqueue_message(msg("a"), Everywhere(1));
		MessageQueue::enqueue_message(msg("b"), Everywhere(2));
		MessageQueue::enqueue_message(msg("c"), Everywhere(3));
		MessageQueue::do_try_state().unwrap();
		println!("{}", MessageQueue::debug_info());
		// service head is 1, it will process a, leaving service head at 2. it also processes b and
		// empties queue 2, so service head will end at 3.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		MessageQueue::enqueue_message(msg("d"), Everywhere(2));
		// service head is 3, so will process c first, then d.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());

		assert_eq!(
			MessagesProcessed::get(),
			vec![
				(vmsg("a"), Everywhere(1)),
				(vmsg("b"), Everywhere(2)),
				(vmsg("c"), Everywhere(3)),
				(vmsg("d"), Everywhere(2)),
			]
		);
	});
}

#[test]
fn service_queues_basic_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		MessageQueue::enqueue_messages(vec![msg("a"), msg("ab"), msg("abc")].into_iter(), Here);
		MessageQueue::enqueue_messages(vec![msg("x"), msg("xy"), msg("xyz")].into_iter(), There);
		assert_eq!(QueueChanges::take(), vec![(Here, 3, 6), (There, 3, 6)]);

		// Service one message from `Here`.
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("a"), Here)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 2, 5)]);

		// Service one message from `There`.
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("x"), There)]);
		assert_eq!(QueueChanges::take(), vec![(There, 2, 5)]);

		// Service the remaining from `Here`.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("ab"), Here), (vmsg("abc"), Here)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 0, 0)]);

		// Service all remaining messages.
		assert_eq!(MessageQueue::service_queues(Weight::MAX), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("xy"), There), (vmsg("xyz"), There)]);
		assert_eq!(QueueChanges::take(), vec![(There, 0, 0)]);
		MessageQueue::do_try_state().unwrap();
	});
}

#[test]
fn service_queues_failing_messages_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		set_weight("service_page_item", 1.into_weight());
		MessageQueue::enqueue_message(msg("badformat"), Here);
		MessageQueue::enqueue_message(msg("corrupt"), Here);
		MessageQueue::enqueue_message(msg("unsupported"), Here);
		MessageQueue::enqueue_message(msg("yield"), Here);
		// Starts with four pages.
		assert_pages(&[0, 1, 2, 3]);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_last_event::<Test>(
			Event::ProcessingFailed {
				id: blake2_256(b"badformat"),
				origin: MessageOrigin::Here,
				error: ProcessMessageError::BadFormat,
			}
			.into(),
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_last_event::<Test>(
			Event::ProcessingFailed {
				id: blake2_256(b"corrupt"),
				origin: MessageOrigin::Here,
				error: ProcessMessageError::Corrupt,
			}
			.into(),
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_last_event::<Test>(
			Event::ProcessingFailed {
				id: blake2_256(b"unsupported"),
				origin: MessageOrigin::Here,
				error: ProcessMessageError::Unsupported,
			}
			.into(),
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(System::events().len(), 3);
		// Last page with the `yield` stays in.
		assert_pages(&[3]);
	});
}

#[test]
fn service_queues_suspension_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		MessageQueue::enqueue_messages(vec![msg("a"), msg("b"), msg("c")].into_iter(), Here);
		MessageQueue::enqueue_messages(vec![msg("x"), msg("y"), msg("z")].into_iter(), There);
		MessageQueue::enqueue_messages(
			vec![msg("m"), msg("n"), msg("o")].into_iter(),
			Everywhere(0),
		);
		assert_eq!(QueueChanges::take(), vec![(Here, 3, 3), (There, 3, 3), (Everywhere(0), 3, 3)]);

		// Service one message from `Here`.
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("a"), Here)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 2, 2)]);

		// Make queue `Here` and `Everywhere(0)` yield.
		YieldingQueues::set(vec![Here, Everywhere(0)]);

		// Service one message from `There`.
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("x"), There)]);
		assert_eq!(QueueChanges::take(), vec![(There, 2, 2)]);

		// Now it would normally swap to `Everywhere(0)` and `Here`, but they are paused so we
		// expect `There` again.
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("y"), There), (vmsg("z"), There)]);

		// Processing with max-weight won't do anything.
		assert_eq!(MessageQueue::service_queues(Weight::MAX), Weight::zero());
		assert_eq!(MessageQueue::service_queues(Weight::MAX), Weight::zero());

		// ... until we resume `Here`:
		YieldingQueues::set(vec![Everywhere(0)]);
		assert_eq!(MessageQueue::service_queues(Weight::MAX), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("b"), Here), (vmsg("c"), Here)]);

		// Everywhere still won't move.
		assert_eq!(MessageQueue::service_queues(Weight::MAX), Weight::zero());
		YieldingQueues::take();
		// Resume `Everywhere(0)` makes it work.
		assert_eq!(MessageQueue::service_queues(Weight::MAX), 3.into_weight());
		assert_eq!(
			MessagesProcessed::take(),
			vec![
				(vmsg("m"), Everywhere(0)),
				(vmsg("n"), Everywhere(0)),
				(vmsg("o"), Everywhere(0))
			]
		);
	});
}

#[test]
fn reap_page_permanent_overweight_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		// Create 10 pages more than the stale limit.
		let n = (MaxStale::get() + 10) as usize;
		for _ in 0..n {
			MessageQueue::enqueue_message(msg("weight=2"), Here);
		}
		assert_eq!(Pages::<Test>::iter().count(), n);
		assert_eq!(QueueChanges::take().len(), n);
		// Mark all pages as stale since their message is permanently overweight.
		MessageQueue::service_queues(1.into_weight());

		// Check that we can reap everything below the watermark.
		let max_stale = MaxStale::get();
		for i in 0..n as u32 {
			let b = BookStateFor::<Test>::get(Here);
			let stale_pages = n as u32 - i;
			let overflow = stale_pages.saturating_sub(max_stale + 1) + 1;
			let backlog = (max_stale * max_stale / overflow).max(max_stale);
			let watermark = b.begin.saturating_sub(backlog);

			if i >= watermark {
				break
			}
			assert_ok!(MessageQueue::do_reap_page(&Here, i));
			assert_eq!(QueueChanges::take(), vec![(Here, b.message_count - 1, b.size - 8)]);
		}

		// Cannot reap any more pages.
		for (o, i, _) in Pages::<Test>::iter() {
			assert_noop!(MessageQueue::do_reap_page(&o, i), Error::<Test>::NotReapable);
			assert!(QueueChanges::take().is_empty());
		}
	});
}

#[test]
fn reaping_overweight_fails_properly() {
	use MessageOrigin::*;
	assert_eq!(MaxStale::get(), 2, "The stale limit is two");

	build_and_execute::<Test>(|| {
		// page 0
		MessageQueue::enqueue_message(msg("weight=4"), Here);
		MessageQueue::enqueue_message(msg("a"), Here);
		// page 1
		MessageQueue::enqueue_message(msg("weight=4"), Here);
		MessageQueue::enqueue_message(msg("b"), Here);
		// page 2
		MessageQueue::enqueue_message(msg("weight=4"), Here);
		MessageQueue::enqueue_message(msg("c"), Here);
		// page 3
		MessageQueue::enqueue_message(msg("bigbig 1"), Here);
		// page 4
		MessageQueue::enqueue_message(msg("bigbig 2"), Here);
		// page 5
		MessageQueue::enqueue_message(msg("bigbig 3"), Here);
		// Double-check that exactly these pages exist.
		assert_pages(&[0, 1, 2, 3, 4, 5]);

		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("a"), Here), (vmsg("b"), Here)]);
		// 2 stale now.

		// Nothing reapable yet, because we haven't hit the stale limit.
		for (o, i, _) in Pages::<Test>::iter() {
			assert_noop!(MessageQueue::do_reap_page(&o, i), Error::<Test>::NotReapable);
		}
		assert_pages(&[0, 1, 2, 3, 4, 5]);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("c"), Here)]);
		// 3 stale now: can take something 4 pages in history.

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("bigbig 1"), Here)]);

		// Nothing reapable yet, because we haven't hit the stale limit.
		for (o, i, _) in Pages::<Test>::iter() {
			assert_noop!(MessageQueue::do_reap_page(&o, i), Error::<Test>::NotReapable);
		}
		assert_pages(&[0, 1, 2, 4, 5]);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("bigbig 2"), Here)]);
		assert_pages(&[0, 1, 2, 5]);

		// First is now reapable as it is too far behind the first ready page (5).
		assert_ok!(MessageQueue::do_reap_page(&Here, 0));
		// Others not reapable yet, because we haven't hit the stale limit.
		for (o, i, _) in Pages::<Test>::iter() {
			assert_noop!(MessageQueue::do_reap_page(&o, i), Error::<Test>::NotReapable);
		}
		assert_pages(&[1, 2, 5]);

		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("bigbig 3"), Here)]);

		assert_noop!(MessageQueue::do_reap_page(&Here, 0), Error::<Test>::NoPage);
		assert_noop!(MessageQueue::do_reap_page(&Here, 3), Error::<Test>::NoPage);
		assert_noop!(MessageQueue::do_reap_page(&Here, 4), Error::<Test>::NoPage);
		// Still not reapable, since the number of stale pages is only 2.
		for (o, i, _) in Pages::<Test>::iter() {
			assert_noop!(MessageQueue::do_reap_page(&o, i), Error::<Test>::NotReapable);
		}
	});
}

#[test]
fn service_queue_bails() {
	// Not enough weight for `service_queue_base`.
	build_and_execute::<Test>(|| {
		set_weight("service_queue_base", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		assert_storage_noop!(MessageQueue::service_queue(0u32.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed().is_zero());
	});
	// Not enough weight for `ready_ring_unknit`.
	build_and_execute::<Test>(|| {
		set_weight("ready_ring_unknit", 2.into_weight());
		let mut meter = WeightMeter::from_limit(1.into_weight());

		assert_storage_noop!(MessageQueue::service_queue(0u32.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed().is_zero());
	});
	// Not enough weight for `service_queue_base` and `ready_ring_unknit`.
	build_and_execute::<Test>(|| {
		set_weight("service_queue_base", 2.into_weight());
		set_weight("ready_ring_unknit", 2.into_weight());

		let mut meter = WeightMeter::from_limit(3.into_weight());
		assert_storage_noop!(MessageQueue::service_queue(0.into(), &mut meter, Weight::MAX));
		assert!(meter.consumed().is_zero());
	});
}

#[test]
fn service_page_works() {
	use super::integration_test::Test; // Run with larger page size.
	use MessageOrigin::*;
	use PageExecutionStatus::*;
	build_and_execute::<Test>(|| {
		set_weight("service_page_base_completion", 2.into_weight());
		set_weight("service_page_item", 3.into_weight());

		let (page, mut msgs) = full_page::<Test>();
		assert!(msgs >= 10, "pre-condition: need at least 10 msgs per page");
		let mut book = book_for::<Test>(&page);
		Pages::<Test>::insert(Here, 0, page);

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
		assert_pages(&[]);
	});
}

// `service_page` does nothing when called with an insufficient weight limit.
#[test]
fn service_page_bails() {
	// Not enough weight for `service_page_base_completion`.
	build_and_execute::<Test>(|| {
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
		assert!(meter.consumed().is_zero());
	});
	// Not enough weight for `service_page_base_no_completion`.
	build_and_execute::<Test>(|| {
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
		assert!(meter.consumed().is_zero());
	});
}

#[test]
fn service_page_item_bails() {
	build_and_execute::<Test>(|| {
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
			ItemExecutionStatus::Bailed
		);
	});
}

#[test]
fn service_page_suspension_works() {
	use super::integration_test::Test; // Run with larger page size.
	use MessageOrigin::*;
	use PageExecutionStatus::*;

	build_and_execute::<Test>(|| {
		let (page, mut msgs) = full_page::<Test>();
		assert!(msgs >= 10, "pre-condition: need at least 10 msgs per page");
		let mut book = book_for::<Test>(&page);
		Pages::<Test>::insert(Here, 0, page);

		// First we process 5 messages from this page.
		let mut meter = WeightMeter::from_limit(5.into_weight());
		let (_, status) =
			crate::Pallet::<Test>::service_page(&Here, &mut book, &mut meter, Weight::MAX);

		assert_eq!(NumMessagesProcessed::take(), 5);
		assert!(meter.remaining().is_zero());
		assert_eq!(status, Bailed); // It bailed since weight is missing.
		msgs -= 5;

		// Then we pause the queue.
		YieldingQueues::set(vec![Here]);
		// Noting happens...
		for _ in 0..5 {
			let (_, status) = crate::Pallet::<Test>::service_page(
				&Here,
				&mut book,
				&mut WeightMeter::max_limit(),
				Weight::MAX,
			);
			assert_eq!(status, NoProgress);
			assert!(NumMessagesProcessed::take().is_zero());
		}

		// Resume and process all remaining.
		YieldingQueues::take();
		let (_, status) = crate::Pallet::<Test>::service_page(
			&Here,
			&mut book,
			&mut WeightMeter::max_limit(),
			Weight::MAX,
		);
		assert_eq!(status, NoMore);
		assert_eq!(NumMessagesProcessed::take(), msgs);

		assert!(Pages::<Test>::iter_keys().count().is_zero());
	});
}

#[test]
fn bump_service_head_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		build_triple_ring();

		// Bump 99 times.
		for i in 0..99 {
			let current = MessageQueue::bump_service_head(&mut WeightMeter::max_limit()).unwrap();
			assert_eq!(current, [Here, There, Everywhere(0)][i % 3]);
		}

		// The ready ring is intact and the service head is still `Here`.
		assert_ring(&[Here, There, Everywhere(0)]);
	});
}

/// `bump_service_head` does nothing when called with an insufficient weight limit.
#[test]
fn bump_service_head_bails() {
	build_and_execute::<Test>(|| {
		set_weight("bump_service_head", 2.into_weight());
		setup_bump_service_head::<Test>(0.into(), 1.into());

		let _guard = StorageNoopGuard::default();
		let mut meter = WeightMeter::from_limit(1.into_weight());
		assert!(MessageQueue::bump_service_head(&mut meter).is_none());
		assert_eq!(meter.consumed(), 0.into_weight());
	});
}

#[test]
fn bump_service_head_trivial_works() {
	build_and_execute::<Test>(|| {
		set_weight("bump_service_head", 2.into_weight());
		let mut meter = WeightMeter::max_limit();

		assert_eq!(MessageQueue::bump_service_head(&mut meter), None, "Cannot bump");
		assert_eq!(meter.consumed(), 2.into_weight());

		setup_bump_service_head::<Test>(0.into(), 1.into());

		assert_eq!(MessageQueue::bump_service_head(&mut meter), Some(0.into()));
		assert_eq!(ServiceHead::<Test>::get().unwrap(), 1.into(), "Bumped the head");
		assert_eq!(meter.consumed(), 4.into_weight());

		assert_eq!(MessageQueue::bump_service_head(&mut meter), Some(1.into()), "Its a ring");
		assert_eq!(meter.consumed(), 6.into_weight());
	});
}

#[test]
fn bump_service_head_no_head_noops() {
	build_and_execute::<Test>(|| {
		build_triple_ring();

		// But remove the service head.
		ServiceHead::<Test>::kill();

		// Nothing happens.
		assert_storage_noop!(MessageQueue::bump_service_head(&mut WeightMeter::max_limit()));
	});
}

#[test]
fn service_page_item_consumes_correct_weight() {
	build_and_execute::<Test>(|| {
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
			ItemExecutionStatus::Executed(true)
		);
		assert_eq!(weight.consumed(), 5.into_weight());
	});
}

/// `service_page_item` skips a permanently `Overweight` message and marks it as `unprocessed`.
#[test]
fn service_page_item_skips_perm_overweight_message() {
	build_and_execute::<Test>(|| {
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
			ItemExecutionStatus::Executed(false)
		);
		assert_eq!(weight.consumed(), 2.into_weight());
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				id: blake2_256(b"TooMuch"),
				origin: MessageOrigin::Here,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);

		// Check that the message was skipped.
		let (pos, processed, payload) = page.peek_index(0).unwrap();
		assert_eq!(pos, 0);
		assert!(!processed);
		assert_eq!(payload, b"TooMuch".encode());
	});
}

#[test]
fn peek_index_works() {
	use super::integration_test::Test; // Run with larger page size.
	build_and_execute::<Test>(|| {
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
fn peek_first_and_skip_first_works() {
	use super::integration_test::Test; // Run with larger page size.
	build_and_execute::<Test>(|| {
		// Fill a page with messages.
		let (mut page, msgs) = full_page::<Test>();

		for i in 0..msgs {
			let msg = page.peek_first().unwrap();
			// `full_page` uses the index as payload.
			assert_eq!(msg.deref(), (i as u32).encode());
			page.skip_first(i % 2 == 0); // True of False should not matter here.
		}
		assert!(page.peek_first().is_none(), "Page must be at the end");

		// Check that all messages were correctly marked as (un)processed.
		for i in 0..msgs {
			let (_, processed, _) = page.peek_index(i).unwrap();
			assert_eq!(processed, i % 2 == 0);
		}
	});
}

#[test]
fn note_processed_at_pos_works() {
	use super::integration_test::Test; // Run with larger page size.
	build_and_execute::<Test>(|| {
		let (mut page, msgs) = full_page::<Test>();

		for i in 0..msgs {
			let (pos, processed, _) = page.peek_index(i).unwrap();
			assert!(!processed);
			assert_eq!(page.remaining as usize, msgs - i);

			page.note_processed_at_pos(pos);

			let (_, processed, _) = page.peek_index(i).unwrap();
			assert!(processed);
			assert_eq!(page.remaining as usize, msgs - i - 1);
		}
		// `skip_first` still works fine.
		for _ in 0..msgs {
			page.peek_first().unwrap();
			page.skip_first(false);
		}
		assert!(page.peek_first().is_none());
	});
}

#[test]
fn note_processed_at_pos_idempotent() {
	let (mut page, _) = full_page::<Test>();
	page.note_processed_at_pos(0);

	let original = page.clone();
	page.note_processed_at_pos(0);
	assert_eq!(page.heap, original.heap);
}

#[test]
fn is_complete_works() {
	use super::integration_test::Test; // Run with larger page size.
	build_and_execute::<Test>(|| {
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
			assert!(processed);
		}
	});
}

#[test]
fn page_from_message_basic_works() {
	assert!(MaxMessageLenOf::<Test>::get() > 0, "pre-condition unmet");
	let mut msg: BoundedVec<u8, MaxMessageLenOf<Test>> = Default::default();
	msg.bounded_resize(MaxMessageLenOf::<Test>::get() as usize, 123);

	let page = PageOf::<Test>::from_message::<Test>(msg.as_bounded_slice());
	assert_eq!(page.remaining, 1);
	assert_eq!(page.remaining_size as usize, msg.len());
	assert!(page.first_index == 0 && page.first == 0 && page.last == 0);

	// Verify the content of the heap.
	let mut heap = Vec::<u8>::new();
	let header =
		ItemHeader::<<Test as Config>::Size> { payload_len: msg.len() as u32, is_processed: false };
	heap.extend(header.encode());
	heap.extend(msg.deref());
	assert_eq!(page.heap, heap);
}

#[test]
fn page_try_append_message_basic_works() {
	use super::integration_test::Test; // Run with larger page size.

	let mut page = PageOf::<Test>::default();
	let mut msgs = 0;
	// Append as many 4-byte message as possible.
	for i in 0..u32::MAX {
		let r = i.using_encoded(|i| page.try_append_message::<Test>(i.try_into().unwrap()));
		if r.is_err() {
			break
		} else {
			msgs += 1;
		}
	}
	let expected_msgs = (<Test as Config>::HeapSize::get()) /
		(ItemHeader::<<Test as Config>::Size>::max_encoded_len() as u32 + 4);
	assert_eq!(expected_msgs, msgs, "Wrong number of messages");
	assert_eq!(page.remaining, msgs);
	assert_eq!(page.remaining_size, msgs * 4);

	// Verify that the heap content is correct.
	let mut heap = Vec::<u8>::new();
	for i in 0..msgs {
		let header = ItemHeader::<<Test as Config>::Size> { payload_len: 4, is_processed: false };
		heap.extend(header.encode());
		heap.extend(i.encode());
	}
	assert_eq!(page.heap, heap);
}

#[test]
fn page_try_append_message_max_msg_len_works_works() {
	use super::integration_test::Test; // Run with larger page size.

	// We start off with an empty page.
	let mut page = PageOf::<Test>::default();
	// … and append a message with maximum possible length.
	let msg = vec![123u8; MaxMessageLenOf::<Test>::get() as usize];
	// … which works.
	page.try_append_message::<Test>(BoundedSlice::defensive_truncate_from(&msg))
		.unwrap();
	// Now we cannot append *anything* since the heap is full.
	page.try_append_message::<Test>(BoundedSlice::defensive_truncate_from(&[]))
		.unwrap_err();
	assert_eq!(page.heap.len(), <Test as Config>::HeapSize::get() as usize);
}

#[test]
fn page_try_append_message_with_remaining_size_works_works() {
	use super::integration_test::Test; // Run with larger page size.
	let header_size = ItemHeader::<<Test as Config>::Size>::max_encoded_len();

	// We start off with an empty page.
	let mut page = PageOf::<Test>::default();
	let mut remaining = <Test as Config>::HeapSize::get() as usize;
	let mut msgs = Vec::new();
	let mut rng = StdRng::seed_from_u64(42);
	// Now we keep appending messages with different lengths.
	while remaining >= header_size {
		let take = rng.gen_range(0..=(remaining - header_size));
		let msg = vec![123u8; take];
		page.try_append_message::<Test>(BoundedSlice::defensive_truncate_from(&msg))
			.unwrap();
		remaining -= take + header_size;
		msgs.push(msg);
	}
	// Cannot even fit a single header in there now.
	assert!(remaining < header_size);
	assert_eq!(<Test as Config>::HeapSize::get() as usize - page.heap.len(), remaining);
	assert_eq!(page.remaining as usize, msgs.len());
	assert_eq!(
		page.remaining_size as usize,
		msgs.iter().fold(0, |mut a, m| {
			a += m.len();
			a
		})
	);
	// Verify the heap content.
	let mut heap = Vec::new();
	for msg in msgs.into_iter() {
		let header = ItemHeader::<<Test as Config>::Size> {
			payload_len: msg.len() as u32,
			is_processed: false,
		};
		heap.extend(header.encode());
		heap.extend(msg);
	}
	assert_eq!(page.heap, heap);
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
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		build_triple_ring();
		QueueChanges::take();

		let book = BookStateFor::<Test>::get(Here);
		assert!(book.begin != book.end);
		// Removing the service head works
		assert_eq!(ServiceHead::<Test>::get(), Some(Here));
		MessageQueue::sweep_queue(Here);
		assert_ring(&[There, Everywhere(0)]);
		// The book still exits, but has updated begin and end.
		let book = BookStateFor::<Test>::get(Here);
		assert_eq!(book.begin, book.end);

		// Removing something that is not the service head works.
		assert!(ServiceHead::<Test>::get() != Some(Everywhere(0)));
		MessageQueue::sweep_queue(Everywhere(0));
		assert_ring(&[There]);
		// The book still exits, but has updated begin and end.
		let book = BookStateFor::<Test>::get(Everywhere(0));
		assert_eq!(book.begin, book.end);

		MessageQueue::sweep_queue(There);
		// The book still exits, but has updated begin and end.
		let book = BookStateFor::<Test>::get(There);
		assert_eq!(book.begin, book.end);
		assert_ring(&[]);

		// Sweeping a queue never calls OnQueueChanged.
		assert!(QueueChanges::take().is_empty());
	})
}

/// Test that `sweep_queue` also works if the ReadyRing wraps around.
#[test]
fn sweep_queue_wraps_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		build_ring::<Test>(&[Here]);

		MessageQueue::sweep_queue(Here);
		let book = BookStateFor::<Test>::get(Here);
		assert!(book.ready_neighbours.is_none());
	});
}

#[test]
fn sweep_queue_invalid_noops() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		assert_storage_noop!(MessageQueue::sweep_queue(Here));
	});
}

#[test]
fn footprint_works() {
	build_and_execute::<Test>(|| {
		let origin = MessageOrigin::Here;
		let (page, msgs) = full_page::<Test>();
		let book = book_for::<Test>(&page);
		BookStateFor::<Test>::insert(origin, book);

		let info = MessageQueue::footprint(origin);
		assert_eq!(info.count as usize, msgs);
		assert_eq!(info.size, page.remaining_size as u64);

		// Sweeping a queue never calls OnQueueChanged.
		assert!(QueueChanges::take().is_empty());
	})
}

/// The footprint of an invalid queue is the default footprint.
#[test]
fn footprint_invalid_works() {
	build_and_execute::<Test>(|| {
		let origin = MessageOrigin::Here;
		assert_eq!(MessageQueue::footprint(origin), Default::default());
	})
}

/// The footprint of a swept queue is still correct.
#[test]
fn footprint_on_swept_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		let mut book = empty_book::<Test>();
		book.message_count = 3;
		book.size = 10;
		BookStateFor::<Test>::insert(Here, &book);
		knit(&Here);

		MessageQueue::sweep_queue(Here);
		let fp = MessageQueue::footprint(Here);
		assert_eq!(fp.count, 3);
		assert_eq!(fp.size, 10);
	})
}

#[test]
fn execute_overweight_works() {
	build_and_execute::<Test>(|| {
		set_weight("bump_service_head", 1.into_weight());
		set_weight("service_queue_base", 1.into_weight());
		set_weight("service_page_base_completion", 1.into_weight());

		// Enqueue a message
		let origin = MessageOrigin::Here;
		MessageQueue::enqueue_message(msg("weight=6"), origin);
		// Load the current book
		let book = BookStateFor::<Test>::get(origin);
		assert_eq!(book.message_count, 1);
		assert!(Pages::<Test>::contains_key(origin, 0));

		// Mark the message as permanently overweight.
		assert_eq!(MessageQueue::service_queues(4.into_weight()), 4.into_weight());
		assert_eq!(QueueChanges::take(), vec![(origin, 1, 8)]);
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				id: blake2_256(b"weight=6"),
				origin: MessageOrigin::Here,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);

		// Now try to execute it with too few weight.
		let consumed =
			<MessageQueue as ServiceQueues>::execute_overweight(5.into_weight(), (origin, 0, 0));
		assert_eq!(consumed, Err(ExecuteOverweightError::InsufficientWeight));

		// Execute it with enough weight.
		assert_eq!(Pages::<Test>::iter().count(), 1);
		assert!(QueueChanges::take().is_empty());
		let consumed =
			<MessageQueue as ServiceQueues>::execute_overweight(7.into_weight(), (origin, 0, 0))
				.unwrap();
		assert_eq!(consumed, 6.into_weight());
		assert_eq!(QueueChanges::take(), vec![(origin, 0, 0)]);
		// There is no message left in the book.
		let book = BookStateFor::<Test>::get(origin);
		assert_eq!(book.message_count, 0);
		// And no more pages.
		assert_eq!(Pages::<Test>::iter().count(), 0);

		// Doing it again with enough weight will error.
		let consumed =
			<MessageQueue as ServiceQueues>::execute_overweight(70.into_weight(), (origin, 0, 0));
		assert_eq!(consumed, Err(ExecuteOverweightError::NotFound));
		assert!(QueueChanges::take().is_empty());
		assert!(!Pages::<Test>::contains_key(origin, 0), "Page is gone");
		// The book should have been unknit from the ready ring.
		assert!(!ServiceHead::<Test>::exists(), "No ready book");
	});
}

#[test]
fn permanently_overweight_book_unknits() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		set_weight("bump_service_head", 1.into_weight());
		set_weight("service_queue_base", 1.into_weight());
		set_weight("service_page_base_completion", 1.into_weight());

		MessageQueue::enqueue_messages([msg("weight=9")].into_iter(), Here);

		// It is the only ready book.
		assert_ring(&[Here]);
		// Mark the message as overweight.
		assert_eq!(MessageQueue::service_queues(8.into_weight()), 4.into_weight());
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				id: blake2_256(b"weight=9"),
				origin: Here,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);
		// The book is not ready anymore.
		assert_ring(&[]);
		assert_eq!(MessagesProcessed::take().len(), 0);
		assert_eq!(BookStateFor::<Test>::get(Here).message_count, 1);
		// Now if we enqueue another message, it will become ready again.
		MessageQueue::enqueue_messages([msg("weight=1")].into_iter(), Here);
		assert_ring(&[Here]);
		assert_eq!(MessageQueue::service_queues(8.into_weight()), 5.into_weight());
		assert_eq!(MessagesProcessed::take().len(), 1);
		assert_ring(&[]);
	});
}

#[test]
fn permanently_overweight_book_unknits_multiple() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		set_weight("bump_service_head", 1.into_weight());
		set_weight("service_queue_base", 1.into_weight());
		set_weight("service_page_base_completion", 1.into_weight());

		MessageQueue::enqueue_messages(
			[msg("weight=1"), msg("weight=9"), msg("weight=9")].into_iter(),
			Here,
		);

		assert_ring(&[Here]);
		// Process the first message.
		assert_eq!(MessageQueue::service_queues(4.into_weight()), 4.into_weight());
		assert_eq!(num_overweight_enqueued_events(), 0);
		assert_eq!(MessagesProcessed::take().len(), 1);

		// Book is still ready since it was not marked as overweight yet.
		assert_ring(&[Here]);
		assert_eq!(MessageQueue::service_queues(8.into_weight()), 5.into_weight());
		assert_eq!(num_overweight_enqueued_events(), 2);
		assert_eq!(MessagesProcessed::take().len(), 0);
		// Now it is overweight.
		assert_ring(&[]);
		// Enqueue another message.
		MessageQueue::enqueue_messages([msg("weight=1")].into_iter(), Here);
		assert_ring(&[Here]);
		assert_eq!(MessageQueue::service_queues(4.into_weight()), 4.into_weight());
		assert_eq!(MessagesProcessed::take().len(), 1);
		assert_ring(&[]);
	});
}

/// We don't want empty books in the ready ring, but if they somehow make their way in there, it
/// should not panic.
#[test]
#[cfg(not(debug_assertions))] // Would trigger a defensive failure otherwise.
fn ready_but_empty_does_not_panic() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		BookStateFor::<Test>::insert(Here, empty_book::<Test>());
		BookStateFor::<Test>::insert(There, empty_book::<Test>());

		knit(&Here);
		knit(&There);
		assert_ring(&[Here, There]);

		assert_eq!(MessageQueue::service_queues(Weight::MAX), 0.into_weight());
		assert_ring(&[]);
	});
}

/// We don't want permanently books in the ready ring, but if they somehow make their way in there,
/// it should not panic.
#[test]
#[cfg(not(debug_assertions))] // Would trigger a defensive failure otherwise.
fn ready_but_perm_overweight_does_not_panic() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		MessageQueue::enqueue_message(msg("weight=9"), Here);
		assert_eq!(MessageQueue::service_queues(8.into_weight()), 0.into_weight());
		assert_ring(&[]);
		// Force it back into the ready ring.
		knit(&Here);
		assert_ring(&[Here]);
		assert_eq!(MessageQueue::service_queues(Weight::MAX), 0.into_weight());
		// Unready again.
		assert_ring(&[]);
	});
}

/// Checks that (un)knitting the ready ring works with just one queue.
///
/// This case is interesting since it wraps and a lot of `mutate` now operate on the same object.
#[test]
fn ready_ring_knit_basic_works() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		BookStateFor::<Test>::insert(Here, empty_book::<Test>());

		for i in 0..10 {
			if i % 2 == 0 {
				knit(&Here);
				assert_ring(&[Here]);
			} else {
				unknit(&Here);
				assert_ring(&[]);
			}
		}
		assert_ring(&[]);
	});
}

#[test]
fn ready_ring_knit_and_unknit_works() {
	use MessageOrigin::*;

	build_and_execute::<Test>(|| {
		// Place three queues into the storage.
		BookStateFor::<Test>::insert(Here, empty_book::<Test>());
		BookStateFor::<Test>::insert(There, empty_book::<Test>());
		BookStateFor::<Test>::insert(Everywhere(0), empty_book::<Test>());

		// Pausing should make no difference:
		PausedQueues::set(vec![Here, There, Everywhere(0)]);

		// Knit them into the ready ring.
		assert_ring(&[]);
		knit(&Here);
		assert_ring(&[Here]);
		knit(&There);
		assert_ring(&[Here, There]);
		knit(&Everywhere(0));
		assert_ring(&[Here, There, Everywhere(0)]);

		// Now unknit…
		unknit(&Here);
		assert_ring(&[There, Everywhere(0)]);
		unknit(&There);
		assert_ring(&[Everywhere(0)]);
		unknit(&Everywhere(0));
		assert_ring(&[]);
	});
}

#[test]
fn enqueue_message_works() {
	use MessageOrigin::*;
	let max_msg_per_page = <Test as Config>::HeapSize::get() as u64 /
		(ItemHeader::<<Test as Config>::Size>::max_encoded_len() as u64 + 1);

	build_and_execute::<Test>(|| {
		// Enqueue messages which should fill three pages.
		let n = max_msg_per_page * 3;
		for i in 1..=n {
			MessageQueue::enqueue_message(msg("a"), Here);
			assert_eq!(QueueChanges::take(), vec![(Here, i, i)], "OnQueueChanged not called");
		}
		assert_eq!(Pages::<Test>::iter().count(), 3);

		// Enqueue one more onto page 4.
		MessageQueue::enqueue_message(msg("abc"), Here);
		assert_eq!(QueueChanges::take(), vec![(Here, n + 1, n + 3)]);
		assert_eq!(Pages::<Test>::iter().count(), 4);

		// Check the state.
		assert_eq!(BookStateFor::<Test>::iter().count(), 1);
		let book = BookStateFor::<Test>::get(Here);
		assert_eq!(book.message_count, n + 1);
		assert_eq!(book.size, n + 3);
		assert_eq!((book.begin, book.end), (0, 4));
		assert_eq!(book.count as usize, Pages::<Test>::iter().count());
	});
}

#[test]
fn enqueue_messages_works() {
	use MessageOrigin::*;
	let max_msg_per_page = <Test as Config>::HeapSize::get() as u64 /
		(ItemHeader::<<Test as Config>::Size>::max_encoded_len() as u64 + 1);

	build_and_execute::<Test>(|| {
		// Enqueue messages which should fill three pages.
		let n = max_msg_per_page * 3;
		let msgs = vec![msg("a"); n as usize];

		// Now queue all messages at once.
		MessageQueue::enqueue_messages(msgs.into_iter(), Here);
		// The changed handler should only be called once.
		assert_eq!(QueueChanges::take(), vec![(Here, n, n)], "OnQueueChanged not called");
		assert_eq!(Pages::<Test>::iter().count(), 3);

		// Enqueue one more onto page 4.
		MessageQueue::enqueue_message(msg("abc"), Here);
		assert_eq!(QueueChanges::take(), vec![(Here, n + 1, n + 3)]);
		assert_eq!(Pages::<Test>::iter().count(), 4);

		// Check the state.
		assert_eq!(BookStateFor::<Test>::iter().count(), 1);
		let book = BookStateFor::<Test>::get(Here);
		assert_eq!(book.message_count, n + 1);
		assert_eq!(book.size, n + 3);
		assert_eq!((book.begin, book.end), (0, 4));
		assert_eq!(book.count as usize, Pages::<Test>::iter().count());
	});
}

#[test]
fn service_queues_suspend_works() {
	use MessageOrigin::*;
	build_and_execute::<Test>(|| {
		MessageQueue::enqueue_messages(vec![msg("a"), msg("ab"), msg("abc")].into_iter(), Here);
		MessageQueue::enqueue_messages(vec![msg("x"), msg("xy"), msg("xyz")].into_iter(), There);
		assert_eq!(QueueChanges::take(), vec![(Here, 3, 6), (There, 3, 6)]);

		// Pause `Here` - execution starts `There`.
		PausedQueues::set(vec![Here]);
		assert_eq!(
			(true, false),
			(
				<Test as Config>::QueuePausedQuery::is_paused(&Here),
				<Test as Config>::QueuePausedQuery::is_paused(&There)
			)
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("x"), There)]);
		assert_eq!(QueueChanges::take(), vec![(There, 2, 5)]);

		// Unpause `Here` - execution continues `There`.
		PausedQueues::take();
		assert_eq!(
			(false, false),
			(
				<Test as Config>::QueuePausedQuery::is_paused(&Here),
				<Test as Config>::QueuePausedQuery::is_paused(&There)
			)
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("xy"), There)]);
		assert_eq!(QueueChanges::take(), vec![(There, 1, 3)]);

		// Now it swaps to `Here`.
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("a"), Here)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 2, 5)]);

		// Pause `There` - execution continues `Here`.
		PausedQueues::set(vec![There]);
		assert_eq!(
			(false, true),
			(
				<Test as Config>::QueuePausedQuery::is_paused(&Here),
				<Test as Config>::QueuePausedQuery::is_paused(&There)
			)
		);
		assert_eq!(MessageQueue::service_queues(1.into_weight()), 1.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("ab"), Here)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 1, 3)]);

		// Unpause `There` and service all remaining messages.
		PausedQueues::take();
		assert_eq!(
			(false, false),
			(
				<Test as Config>::QueuePausedQuery::is_paused(&Here),
				<Test as Config>::QueuePausedQuery::is_paused(&There)
			)
		);
		assert_eq!(MessageQueue::service_queues(2.into_weight()), 2.into_weight());
		assert_eq!(MessagesProcessed::take(), vec![(vmsg("abc"), Here), (vmsg("xyz"), There)]);
		assert_eq!(QueueChanges::take(), vec![(Here, 0, 0), (There, 0, 0)]);
	});
}

/// Tests that manual overweight execution on a suspended queue errors with `QueueSuspended`.
#[test]
fn execute_overweight_respects_suspension() {
	build_and_execute::<Test>(|| {
		let origin = MessageOrigin::Here;
		MessageQueue::enqueue_message(msg("weight=5"), origin);
		// Mark the message as permanently overweight.
		MessageQueue::service_queues(4.into_weight());
		assert_last_event::<Test>(
			Event::OverweightEnqueued {
				id: blake2_256(b"weight=5"),
				origin,
				message_index: 0,
				page_index: 0,
			}
			.into(),
		);
		PausedQueues::set(vec![origin]);
		assert!(<Test as Config>::QueuePausedQuery::is_paused(&origin));

		// Execution should fail.
		assert_eq!(
			<MessageQueue as ServiceQueues>::execute_overweight(Weight::MAX, (origin, 0, 0)),
			Err(ExecuteOverweightError::QueuePaused)
		);

		PausedQueues::take();
		assert!(!<Test as Config>::QueuePausedQuery::is_paused(&origin));

		// Execution should work again with same args.
		assert_ok!(<MessageQueue as ServiceQueues>::execute_overweight(
			Weight::MAX,
			(origin, 0, 0)
		));

		assert_last_event::<Test>(
			Event::Processed {
				id: blake2_256(b"weight=5"),
				origin,
				weight_used: 5.into_weight(),
				success: true,
			}
			.into(),
		);
	});
}

#[test]
fn service_queue_suspension_ready_ring_works() {
	build_and_execute::<Test>(|| {
		let origin = MessageOrigin::Here;
		PausedQueues::set(vec![origin]);
		MessageQueue::enqueue_message(msg("weight=5"), origin);

		MessageQueue::service_queues(Weight::MAX);
		// It did not execute but is in the ready ring.
		assert!(System::events().is_empty(), "Paused");
		assert_ring(&[origin]);

		// Now when we un-pause, it will execute.
		PausedQueues::take();
		MessageQueue::service_queues(Weight::MAX);
		assert_last_event::<Test>(
			Event::Processed {
				id: blake2_256(b"weight=5"),
				origin,
				weight_used: 5.into_weight(),
				success: true,
			}
			.into(),
		);
	});
}
