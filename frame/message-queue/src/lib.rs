// Copyright 2020-2021 Parity Technologies (UK) Ltd.
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

//! Pallet to handle XCM message queuing.

#![cfg_attr(not(feature = "std"), no_std)]

mod benchmarking;
mod mock;
#[cfg(test)]
mod tests;
pub mod weights;

use codec::{Codec, Decode, Encode, FullCodec, MaxEncodedLen};
use frame_support::{
	defensive,
	pallet_prelude::*,
	traits::{
		DefensiveTruncateFrom, EnqueueMessage, ProcessMessage, ProcessMessageError, ServiceQueues,
	},
	BoundedSlice, CloneNoBound, DefaultNoBound,
};
use frame_system::pallet_prelude::*;
pub use pallet::*;
use scale_info::TypeInfo;
use sp_arithmetic::traits::{BaseArithmetic, Unsigned};
use sp_runtime::{
	traits::{Hash, One, Zero},
	SaturatedConversion, Saturating,
};
use sp_std::{fmt::Debug, ops::Deref, prelude::*, vec};
use sp_weights::WeightCounter;
pub use weights::WeightInfo;

/// Type for identifying an overweight message.
type OverweightIndex = u64;
/// Type for identifying a page.
type PageIndex = u32;

const LOG_TARGET: &'static str = "runtime::message-queue";

/// Data encoded and prefixed to the encoded `MessageItem`.
#[derive(Encode, Decode, PartialEq, MaxEncodedLen, Debug)]
pub struct ItemHeader<Size> {
	/// The length of this item, not including the size of this header. The next item of the page
	/// follows immediately after the payload of this item.
	payload_len: Size,
	/// Whether this item has been processed.
	is_processed: bool,
}

/// A page of messages. Pages always contain at least one item.
#[derive(
	CloneNoBound, Encode, Decode, RuntimeDebugNoBound, DefaultNoBound, TypeInfo, MaxEncodedLen,
)]
#[scale_info(skip_type_params(HeapSize))]
#[codec(mel_bound(Size: MaxEncodedLen))]
pub struct Page<Size: Into<u32> + Debug + Clone + Default, HeapSize: Get<Size>> {
	/// Messages remaining to be processed; this includes overweight messages which have been
	/// skipped.
	remaining: Size,
	/// The heap-offset of the header of the first message item in this page which is ready for
	/// processing.
	first: Size,
	/// The heap-offset of the header of the last message item in this page.
	last: Size,
	/// The heap. If `self.offset == self.heap.len()` then the page is empty and should be deleted.
	heap: BoundedVec<u8, IntoU32<HeapSize, Size>>,
}

impl<
		Size: BaseArithmetic + Unsigned + Copy + Into<u32> + Codec + MaxEncodedLen + Debug + Default,
		HeapSize: Get<Size>,
	> Page<Size, HeapSize>
{
	/// Create a [`Page`] from one unprocessed message and its origin.
	fn from_message<T: Config>(
		message: BoundedSlice<u8, MaxMessageLenOf<T>>,
		origin: BoundedSlice<u8, MaxOriginLenOf<T>>,
	) -> Self {
		let payload_len = origin.len().saturating_add(message.len());
		let data_len = ItemHeader::<Size>::max_encoded_len().saturating_add(payload_len);
		let header =
			ItemHeader::<Size> { payload_len: payload_len.saturated_into(), is_processed: false };

		let mut heap = Vec::with_capacity(data_len);
		header.using_encoded(|h| heap.extend_from_slice(h));
		heap.extend_from_slice(origin.deref());
		heap.extend_from_slice(message.deref());

		Page {
			remaining: One::one(),
			first: Zero::zero(),
			last: Zero::zero(),
			heap: BoundedVec::defensive_truncate_from(heap),
		}
	}

	/// Try to append one message from an origin.
	fn try_append_message<T: Config>(
		&mut self,
		message: BoundedSlice<u8, MaxMessageLenOf<T>>,
		origin: BoundedSlice<u8, MaxOriginLenOf<T>>,
	) -> Result<(), ()> {
		let pos = self.heap.len();
		let payload_len = origin.len().saturating_add(message.len());
		let data_len = ItemHeader::<Size>::max_encoded_len().saturating_add(payload_len);

		let header =
			ItemHeader::<Size> { payload_len: payload_len.saturated_into(), is_processed: false };
		let heap_size: u32 = HeapSize::get().into();
		if (heap_size as usize).saturating_sub(self.heap.len()) < data_len {
			// Can't fit.
			return Err(())
		}

		let mut heap = sp_std::mem::take(&mut self.heap).into_inner();
		header.using_encoded(|h| heap.extend_from_slice(h));
		heap.extend_from_slice(origin.deref());
		heap.extend_from_slice(message.deref());
		self.heap = BoundedVec::defensive_truncate_from(heap);
		self.last = pos.saturated_into();
		self.remaining.saturating_inc();
		Ok(())
	}

	/// Returns the first message in the page without removing it.
	///
	/// SAFETY: Does not panic even on corrupted storage.
	fn peek_first(&self) -> Option<BoundedSlice<u8, IntoU32<HeapSize, Size>>> {
		if self.first > self.last {
			return None
		}
		let f = (self.first.into() as usize).min(self.heap.len());
		let mut item_slice = &self.heap[f..];
		if let Ok(h) = ItemHeader::<Size>::decode(&mut item_slice) {
			let payload_len = h.payload_len.into() as usize;
			if payload_len <= item_slice.len() {
				// impossible to truncate since is sliced up from `self.heap: BoundedVec<u8,
				// HeapSize>`
				return Some(BoundedSlice::defensive_truncate_from(&item_slice[..payload_len]))
			}
		}
		defensive!("message-queue: heap corruption");
		None
	}

	/// Point `first` at the next message, marking the first as processed if `is_processed` is true.
	fn skip_first(&mut self, is_processed: bool) {
		let f = (self.first.into() as usize).min(self.heap.len());
		if let Ok(mut h) = ItemHeader::decode(&mut &self.heap[f..]) {
			if is_processed && !h.is_processed {
				h.is_processed = true;
				h.using_encoded(|d| self.heap[f..f + d.len()].copy_from_slice(d));
				self.remaining.saturating_dec();
			}
			self.first
				.saturating_accrue(ItemHeader::<Size>::max_encoded_len().saturated_into());
			self.first.saturating_accrue(h.payload_len);
		}
	}

	/// Return the unprocessed encoded (origin, message) pair of `index` into the page's
	/// messages if and only if it was skipped (i.e. of location prior to `first`).
	fn peek_index(&self, index: usize) -> Option<(usize, bool, &[u8])> {
		let mut pos = 0;
		let mut item_slice = &self.heap[..];
		let header_len: usize = ItemHeader::<Size>::max_encoded_len().saturated_into();
		for _ in 0..index {
			let h = ItemHeader::<Size>::decode(&mut item_slice).ok()?;
			let item_len = h.payload_len.into() as usize;
			if item_slice.len() < item_len {
				return None
			}
			item_slice = &item_slice[item_len..];
			pos.saturating_accrue(header_len.saturating_add(item_len));
		}
		let h = ItemHeader::<Size>::decode(&mut item_slice).ok()?;
		if item_slice.len() < h.payload_len.into() as usize {
			return None
		}
		item_slice = &item_slice[..h.payload_len.into() as usize];
		Some((pos, h.is_processed, item_slice))
	}

	/// Set the `is_processed` flag for the item at `pos` to be `true` if not already and decrement
	/// the `remaining` counter of the page.
	fn note_processed_at_pos(&mut self, pos: usize) {
		if let Ok(mut h) = ItemHeader::<Size>::decode(&mut &self.heap[pos..]) {
			if !h.is_processed {
				h.is_processed = true;
				h.using_encoded(|d| self.heap[pos..pos + d.len()].copy_from_slice(d));
				self.remaining.saturating_dec();
			}
		}
	}

	fn is_complete(&self) -> bool {
		self.remaining.is_zero()
	}
}

#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct Neighbours<MessageOrigin> {
	prev: MessageOrigin,
	next: MessageOrigin,
}

#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct BookState<MessageOrigin> {
	/// The first page with some items to be processed in it. If this is `>= end`, then there are
	/// no pages with items to be processing in them.
	begin: PageIndex,
	/// One more than the last page with some items to be processed in it.
	end: PageIndex,
	/// The number of pages stored at present.
	count: PageIndex,
	/// If this book has any ready pages, then this will be `Some` with the previous and next
	/// neighbours. This wraps around.
	ready_neighbours: Option<Neighbours<MessageOrigin>>,
}

impl<MessageOrigin> Default for BookState<MessageOrigin> {
	fn default() -> Self {
		Self { begin: 0, end: 0, count: 0, ready_neighbours: None }
	}
}

#[frame_support::pallet]
pub mod pallet {
	use super::*;

	#[pallet::pallet]
	#[pallet::generate_store(pub(super) trait Store)]
	pub struct Pallet<T>(_);

	#[pallet::config]
	/// The module configuration trait.
	pub trait Config: frame_system::Config {
		/// The overarching event type.
		type RuntimeEvent: From<Event<Self>> + IsType<<Self as frame_system::Config>::RuntimeEvent>;

		/// Weight information for extrinsics in this pallet.
		type WeightInfo: WeightInfo;

		/// Processor for a message.
		type MessageProcessor: ProcessMessage;

		/// Page/heap size type.
		type Size: BaseArithmetic
			+ Unsigned
			+ Copy
			+ Into<u32>
			+ Member
			+ Encode
			+ Decode
			+ MaxEncodedLen
			+ TypeInfo
			+ Default;

		/// The size of the page; this implies the maximum message size which can be sent.
		#[pallet::constant]
		type HeapSize: Get<Self::Size>;

		/// The maximum number of stale pages (i.e. of overweight messages) allowed before culling
		/// can happen. Once there are more stale pages than this, then historical pages may be
		/// dropped, even if they contain unprocessed overweight messages.
		#[pallet::constant]
		type MaxStale: Get<u32>;
	}

	#[pallet::event]
	#[pallet::generate_deposit(pub(super) fn deposit_event)]
	pub enum Event<T: Config> {
		/// Message discarded due to an inability to decode the item. Usually caused by state
		/// corruption.
		Discarded {
			hash: T::Hash,
		},
		/// Message discarded due to an error in the `MessageProcessor` (usually a format error).
		ProcessingFailed {
			hash: T::Hash,
			origin: MessageOriginOf<T>,
			error: ProcessMessageError,
		},
		/// Message is processed.
		Processed {
			hash: T::Hash,
			origin: MessageOriginOf<T>,
			weight_used: Weight,
			success: bool,
		},
		/// Message placed in overweight queue.
		Overweight {
			hash: T::Hash,
			origin: MessageOriginOf<T>,
			index: OverweightIndex,
		},
		PageReaped {
			origin: MessageOriginOf<T>,
			index: PageIndex,
		},
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Page is not reapable because it has items remaining to be processed and is not old
		/// enough.
		NotReapable,
		/// Page to be reaped does not exist.
		NoPage,
		NoMessage,
		Unexpected,
		AlreadyProcessed,
		Queued,
		InsufficientWeight,
	}

	/// The index of the first and last (non-empty) pages.
	#[pallet::storage]
	pub(super) type BookStateOf<T: Config> =
		StorageMap<_, Twox64Concat, MessageOriginOf<T>, BookState<MessageOriginOf<T>>, ValueQuery>;

	/// The origin at which we should begin servicing.
	#[pallet::storage]
	pub(super) type ServiceHead<T: Config> = StorageValue<_, MessageOriginOf<T>, OptionQuery>;

	/// The map of page indices to pages.
	#[pallet::storage]
	pub(super) type Pages<T: Config> = StorageDoubleMap<
		_,
		Twox64Concat,
		MessageOriginOf<T>,
		Twox64Concat,
		PageIndex,
		Page<T::Size, T::HeapSize>,
		OptionQuery,
	>;

	#[pallet::hooks]
	impl<T: Config> Hooks<BlockNumberFor<T>> for Pallet<T> {
		fn on_initialize(_n: BlockNumberFor<T>) -> Weight {
			let weight_used = Weight::zero();
			weight_used
		}

		fn integrity_test() {
			// TODO currently disabled since it fails.
			// None of the weight functions can be zero.
			// Otherwise we risk getting stuck in a no-progress situation (= infinite loop).
			/*weights::WeightMetaInfo::<<T as Config>::WeightInfo>::visit_weight_functions(
				|name, w| assert!(!w.is_zero(), "Weight function is zero: {}", name),
			);*/
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		/// Remove a page which has no more messages remaining to be processed.
		#[pallet::weight(150_000_000_000)]
		pub fn reap_page(
			origin: OriginFor<T>,
			message_origin: MessageOriginOf<T>,
			page_index: PageIndex,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			Self::do_reap_page(&message_origin, page_index)
		}

		/// Execute an overweight message.
		///
		/// - `origin`: Must be `Signed`.
		/// - `message_origin`: The origin from which the message to be executed arrived.
		/// - `page`: The page in the queue in which the message to be executed is sitting.
		/// - `index`: The index into the queue of the message to be executed.
		/// - `weight_limit`: The maximum amount of weight allowed to be consumed in the execution
		///   of the message.
		///
		/// Benchmark complexity considerations: O(index + weight_limit).
		#[pallet::weight(150_000_000_000)]
		pub fn execute_overweight(
			origin: OriginFor<T>,
			message_origin: MessageOriginOf<T>,
			page: PageIndex,
			index: T::Size,
			weight_limit: Weight,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			Self::do_execute_overweight(message_origin, page, index, weight_limit)
		}
	}
}

pub struct ReadyRing<T: Config> {
	first: Option<MessageOriginOf<T>>,
	next: Option<MessageOriginOf<T>>,
}
impl<T: Config> ReadyRing<T> {
	fn new() -> Self {
		Self { first: ServiceHead::<T>::get(), next: ServiceHead::<T>::get() }
	}
}
impl<T: Config> Iterator for ReadyRing<T> {
	type Item = MessageOriginOf<T>;
	fn next(&mut self) -> Option<Self::Item> {
		match self.next.take() {
			None => None,
			Some(last) => {
				self.next = BookStateOf::<T>::get(&last)
					.ready_neighbours
					.map(|n| n.next)
					.filter(|n| Some(n) != self.first.as_ref());
				Some(last)
			},
		}
	}
}

/// The status of a page after trying to execute its next message.
#[derive(PartialEq, Debug)]
enum PageExecutionStatus {
	/// The execution bailed because there was not enough weight remaining.
	Bailed,
	/// No more messages could be loaded. This does _not_ imply `page.is_complete()`.
	///
	/// The reasons for this status are:
	///  - The end of the page is reached but there could still be skipped messages.
	///  - The storage is corrupted.
	NoMore,
	/// The execution progressed and executed some messages. The inner is the number of messages
	/// removed from the queue.
	Partial,
}

/// The status of an attempt to process a message.
#[derive(PartialEq)]
enum MessageExecutionStatus {
	/// The message could not be executed due to a format error.
	BadFormat,
	/// There is not enough weight remaining at present.
	InsufficientWeight,
	/// There will never be enough enough weight.
	Overweight,
	/// The message was processed successfully.
	Processed,
	/// The message was processed and resulted in a permanent error.
	Unprocessable,
}

impl<T: Config> Pallet<T> {
	/// Knit `origin` into the ready ring right at the end.
	///
	/// Return the two ready ring neighbours of `origin`.
	fn ready_ring_knit(origin: &MessageOriginOf<T>) -> Result<Neighbours<MessageOriginOf<T>>, ()> {
		if let Some(head) = ServiceHead::<T>::get() {
			let mut head_book_state = BookStateOf::<T>::get(&head);
			let mut head_neighbours = head_book_state.ready_neighbours.take().ok_or(())?;
			let tail = head_neighbours.prev;
			head_neighbours.prev = origin.clone();
			head_book_state.ready_neighbours = Some(head_neighbours);
			BookStateOf::<T>::insert(&head, head_book_state);

			let mut tail_book_state = BookStateOf::<T>::get(&tail);
			let mut tail_neighbours = tail_book_state.ready_neighbours.take().ok_or(())?;
			tail_neighbours.next = origin.clone();
			tail_book_state.ready_neighbours = Some(tail_neighbours);
			BookStateOf::<T>::insert(&tail, tail_book_state);

			Ok(Neighbours { next: head, prev: tail })
		} else {
			ServiceHead::<T>::put(origin);
			Ok(Neighbours { next: origin.clone(), prev: origin.clone() })
		}
	}

	fn ready_ring_unknit(origin: &MessageOriginOf<T>, neighbours: Neighbours<MessageOriginOf<T>>) {
		if origin == &neighbours.next {
			debug_assert!(
				origin == &neighbours.prev,
				"unknitting from single item ring; outgoing must be only item"
			);
			// Service queue empty.
			ServiceHead::<T>::kill();
		} else {
			BookStateOf::<T>::mutate(&neighbours.next, |book_state| {
				if let Some(ref mut n) = book_state.ready_neighbours {
					n.prev = neighbours.prev.clone()
				}
			});
			BookStateOf::<T>::mutate(&neighbours.prev, |book_state| {
				if let Some(ref mut n) = book_state.ready_neighbours {
					n.next = neighbours.next.clone()
				}
			});
			if let Some(head) = ServiceHead::<T>::get() {
				if &head == origin {
					ServiceHead::<T>::put(neighbours.next);
				}
			} else {
				defensive!("`ServiceHead` must be some if there was a ready queue");
			}
		}
	}

	fn bump_service_head(weight: &mut WeightCounter) -> Option<MessageOriginOf<T>> {
		if !weight.check_accrue(T::WeightInfo::bump_service_head()) {
			log::debug!(target: LOG_TARGET, "bump_service_head: weight limit reached");
			return None
		}

		if let Some(head) = ServiceHead::<T>::get() {
			let mut head_book_state = BookStateOf::<T>::get(&head);
			if let Some(head_neighbours) = head_book_state.ready_neighbours.take() {
				ServiceHead::<T>::put(&head_neighbours.next);
				log::debug!(
					target: LOG_TARGET,
					"bump_service_head: next head `{:?}`",
					head_neighbours.next
				);
				Some(head)
			} else {
				None
			}
		} else {
			None
		}
	}

	fn do_enqueue_message(
		origin: &MessageOriginOf<T>,
		message: BoundedSlice<u8, MaxMessageLenOf<T>>,
		origin_data: BoundedSlice<u8, MaxOriginLenOf<T>>,
	) {
		let mut book_state = BookStateOf::<T>::get(origin);
		if book_state.end > book_state.begin {
			debug_assert!(book_state.ready_neighbours.is_some(), "Must be in ready ring if ready");
			// Already have a page in progress - attempt to append.
			let last = book_state.end - 1;
			let mut page = match Pages::<T>::get(origin, last) {
				Some(p) => p,
				None => {
					defensive!("Corruption: referenced page doesn't exist.");
					return
				},
			};
			if let Ok(_) = page.try_append_message::<T>(message, origin_data) {
				Pages::<T>::insert(origin, last, &page);
				return
			}
		} else {
			debug_assert!(
				book_state.ready_neighbours.is_none(),
				"Must not be in ready ring if not ready"
			);
			// insert into ready queue.
			match Self::ready_ring_knit(origin) {
				Ok(neighbours) => book_state.ready_neighbours = Some(neighbours),
				Err(()) => debug_assert!(false, "Ring state invalid when knitting"),
			}
		}
		// No room on the page or no page - link in a new page.
		book_state.end.saturating_inc();
		book_state.count.saturating_inc();
		Pages::<T>::insert(
			origin,
			book_state.end - 1,
			Page::from_message::<T>(message, origin_data),
		);
		BookStateOf::<T>::insert(&origin, book_state);
	}

	pub fn do_execute_overweight(
		origin: MessageOriginOf<T>,
		page_index: PageIndex,
		index: T::Size,
		weight_limit: Weight,
	) -> DispatchResult {
		let mut book_state = BookStateOf::<T>::get(&origin);
		let mut page = Pages::<T>::get(&origin, page_index).ok_or(Error::<T>::NoPage)?;
		let (pos, is_processed, blob) =
			page.peek_index(index.into() as usize).ok_or(Error::<T>::NoMessage)?;
		ensure!(
			page_index < book_state.begin ||
				(page_index == book_state.begin && pos < page.first.into() as usize),
			Error::<T>::Queued
		);
		ensure!(is_processed, Error::<T>::AlreadyProcessed);
		use MessageExecutionStatus::*;
		let mut weight_counter = WeightCounter::from_limit(weight_limit);
		match Self::process_message(blob, &mut weight_counter, weight_limit) {
			Overweight | InsufficientWeight => Err(Error::<T>::InsufficientWeight.into()),
			BadFormat | Unprocessable | Processed => {
				page.note_processed_at_pos(pos);
				if page.remaining.is_zero() {
					Pages::<T>::remove(&origin, page_index);
					debug_assert!(book_state.count >= 1, "page exists, so book must have pages");
					book_state.count.saturating_dec();
				// no need toconsider .first or ready ring since processing an overweight page would
				// not alter that state.
				} else {
					Pages::<T>::insert(&origin, page_index, page);
				}
				Ok(())
			},
		}
	}

	/// Remove a page which has no more messages remaining to be processed.
	fn do_reap_page(origin: &MessageOriginOf<T>, page_index: PageIndex) -> DispatchResult {
		let mut book_state = BookStateOf::<T>::get(origin);
		// definitely not reapable if the page's index is no less than the `begin`ning of ready
		// pages.
		ensure!(page_index < book_state.begin, Error::<T>::NotReapable);

		let page = Pages::<T>::get(origin, page_index).ok_or(Error::<T>::NoPage)?;

		// definitely reapable if the page has no messages in it.
		let reapable = page.remaining.is_zero();

		// also reapable if the page index has dropped below our watermark.
		let cullable = || {
			let total_pages = book_state.count;
			let ready_pages = book_state.end.saturating_sub(book_state.begin).min(total_pages);
			let stale_pages = total_pages - ready_pages;
			let max_stale = T::MaxStale::get();
			let overflow = match stale_pages.checked_sub(max_stale + 1) {
				Some(x) => x + 1,
				None => return false,
			};
			let backlog = (max_stale * max_stale / overflow).max(max_stale);
			let watermark = book_state.begin.saturating_sub(backlog);
			page_index < watermark
		};
		ensure!(reapable || cullable(), Error::<T>::NotReapable);

		Pages::<T>::remove(origin, page_index);
		debug_assert!(book_state.count > 0, "reaping a page implies there are pages");
		book_state.count.saturating_dec();
		BookStateOf::<T>::insert(origin, book_state);
		Self::deposit_event(Event::PageReaped { origin: origin.clone(), index: page_index });

		Ok(())
	}

	/// Execute any messages remaining to be processed in the queue of `origin`, using up to
	/// `weight_limit` to do so. Any messages which would take more than `overweight_limit` to
	/// execute are deemed overweight and ignored.
	fn service_queue(
		origin: MessageOriginOf<T>,
		weight: &mut WeightCounter,
		overweight_limit: Weight,
	) -> Option<MessageOriginOf<T>> {
		if !weight.check_accrue(T::WeightInfo::service_queue_base()) {
			return None
		}

		let mut book_state = BookStateOf::<T>::get(&origin);
		let mut total_processed = 0;
		while book_state.end > book_state.begin {
			let (processed, status) =
				Self::service_page(&origin, &mut book_state, weight, overweight_limit);
			total_processed.saturating_accrue(processed);
			match status {
				// Store the page progress and do not go to the next one.
				PageExecutionStatus::Bailed => break,
				// Go to the next page if this one is at the end.
				PageExecutionStatus::NoMore => (),
				// TODO @ggwpez think of a better enum here.
				PageExecutionStatus::Partial => {
					defensive!("should progress till the end or bail");
				},
			};
			book_state.begin.saturating_inc();
		}
		let next_ready = book_state.ready_neighbours.as_ref().map(|x| x.next.clone());
		if book_state.begin >= book_state.end && total_processed > 0 {
			// No longer ready - unknit.
			if let Some(neighbours) = book_state.ready_neighbours.take() {
				Self::ready_ring_unknit(&origin, neighbours);
			} else {
				debug_assert!(false, "Freshly processed queue must have been ready");
			}
		}
		BookStateOf::<T>::insert(&origin, &book_state);
		next_ready
	}

	/// Service as many messages of a page as possible.
	///
	/// Returns whether the execution bailed.
	fn service_page(
		origin: &MessageOriginOf<T>,
		book_state: &mut BookState<MessageOriginOf<T>>,
		weight: &mut WeightCounter,
		overweight_limit: Weight,
	) -> (u32, PageExecutionStatus) {
		use PageExecutionStatus::*;
		if !weight.check_accrue(T::WeightInfo::service_page_base()) {
			return (0, Bailed)
		}

		let page_index = book_state.begin;
		let mut page = match Pages::<T>::get(&origin, page_index) {
			Some(p) => p,
			None => {
				debug_assert!(false, "message-queue: referenced page not found");
				return (0, NoMore)
			},
		};

		let mut total_processed = 0;

		// Execute as many messages as possible.
		let status = loop {
			match Self::service_page_item(origin, &mut page, weight, overweight_limit) {
				s @ Bailed | s @ NoMore => break s,
				// Keep going as long as we make progress...
				Partial => {
					total_processed.saturating_inc();
					continue
				},
			}
		};

		if page.is_complete() {
			debug_assert!(
				status != PageExecutionStatus::Bailed,
				"we never bail if a page became complete"
			);
			Pages::<T>::remove(&origin, page_index);
			debug_assert!(book_state.count > 0, "completing a page implies there are pages");
			book_state.count.saturating_dec();
		} else {
			Pages::<T>::insert(&origin, page_index, page);
		}
		(total_processed, status)
	}

	/// Execute the next message of a page.
	pub(crate) fn service_page_item(
		_origin: &MessageOriginOf<T>,
		page: &mut PageOf<T>,
		weight: &mut WeightCounter,
		overweight_limit: Weight,
	) -> PageExecutionStatus {
		// This ugly pre-checking is needed for the invariant
		// "we never bail if a page became complete".
		if page.is_complete() {
			return PageExecutionStatus::NoMore
		}
		if !weight.check_accrue(T::WeightInfo::service_page_item()) {
			return PageExecutionStatus::Bailed
		}
		let message = &match page.peek_first() {
			Some(m) => m,
			None => return PageExecutionStatus::NoMore,
		}[..];

		use MessageExecutionStatus::*;
		let is_processed = match Self::process_message(message, weight, overweight_limit) {
			InsufficientWeight => return PageExecutionStatus::Bailed,
			Processed | Unprocessable | BadFormat => true,
			Overweight => false,
		};
		page.skip_first(is_processed);
		PageExecutionStatus::Partial
	}

	/// Print which messages are in each queue.
	///
	/// # Example output
	///
	/// ```text
	///	queue Here:
	///   page 0: []
	/// > page 1: []
	///   page 2: ["\0weight=4", "\0c", ]
	///   page 3: ["\0bigbig 1", ]
	///   page 4: ["\0bigbig 2", ]
	///   page 5: ["\0bigbig 3", ]
	/// ```
	#[cfg(feature = "std")]
	fn debug_info() -> String {
		let mut info = String::new();
		for (origin, book_state) in BookStateOf::<T>::iter() {
			let mut queue = format!("queue {:?}:\n", &origin);	
			let mut pages = Pages::<T>::iter_prefix(&origin).collect::<Vec<_>>();
			pages.sort_by(|(a,_ ), (b, _)| a.cmp(b));
			for (page_index, page) in pages.into_iter() {
				let mut page = page;
				let mut page_info = format!("page {}: [", page_index);
				if book_state.begin == page_index {
					page_info = format!("> {}", page_info);
				} else {
					page_info = format!("  {}", page_info);
				}
				while let Some(message) = page.peek_first() {
					let msg = String::from_utf8_lossy(message.deref());
					page_info.push_str(&format!("{:?}, ", msg));
					page.skip_first(true);
				}
				page_info.push_str("]\n");
				queue.push_str(&page_info);
			}
			info.push_str(&queue);
		}
		info
	}

	fn process_message(
		mut message: &[u8],
		weight: &mut WeightCounter,
		overweight_limit: Weight,
	) -> MessageExecutionStatus {
		match MessageOriginOf::<T>::decode(&mut message) {
			Ok(origin) => {
				let hash = T::Hashing::hash(message);
				use ProcessMessageError::Overweight;
				match T::MessageProcessor::process_message(
					message,
					origin.clone(),
					weight.remaining(),
				) {
					Err(Overweight(w)) if w.any_gt(overweight_limit) => {
						// Permanently overweight.
						Self::deposit_event(Event::<T>::Overweight { hash, origin, index: 0 }); // TODO page + index
						MessageExecutionStatus::Overweight
					},
					Err(Overweight(_)) => {
						// Temporarily overweight - save progress and stop processing this
						// queue.
						MessageExecutionStatus::InsufficientWeight
					},
					Err(error) => {
						// Permanent error - drop
						Self::deposit_event(Event::<T>::ProcessingFailed { hash, origin, error });
						MessageExecutionStatus::Unprocessable
					},
					Ok((success, weight_used)) => {
						// Success
						weight.defensive_saturating_accrue(weight_used);
						let event = Event::<T>::Processed { hash, origin, weight_used, success };
						Self::deposit_event(event);
						MessageExecutionStatus::Processed
					},
				}
			},
			Err(_) => {
				let hash = T::Hashing::hash(message);
				Self::deposit_event(Event::<T>::Discarded { hash });
				MessageExecutionStatus::BadFormat
			},
		}
	}
}

pub struct MaxEncodedLenOf<T>(sp_std::marker::PhantomData<T>);
impl<T: MaxEncodedLen> Get<u32> for MaxEncodedLenOf<T> {
	fn get() -> u32 {
		T::max_encoded_len() as u32
	}
}

pub struct MaxMessageLen<Origin, Size, HeapSize>(
	sp_std::marker::PhantomData<(Origin, Size, HeapSize)>,
);
impl<Origin: MaxEncodedLen, Size: MaxEncodedLen + Into<u32>, HeapSize: Get<Size>> Get<u32>
	for MaxMessageLen<Origin, Size, HeapSize>
{
	fn get() -> u32 {
		(HeapSize::get().into())
			.saturating_sub(Origin::max_encoded_len() as u32)
			.saturating_sub(ItemHeader::<Size>::max_encoded_len() as u32)
	}
}

pub type MaxMessageLenOf<T> =
	MaxMessageLen<MessageOriginOf<T>, <T as Config>::Size, <T as Config>::HeapSize>;
pub type MaxOriginLenOf<T> = MaxEncodedLenOf<MessageOriginOf<T>>;
pub type MessageOriginOf<T> = <<T as Config>::MessageProcessor as ProcessMessage>::Origin;
pub type HeapSizeU32Of<T> = IntoU32<<T as Config>::HeapSize, <T as Config>::Size>;
pub type PageOf<T> = Page<<T as Config>::Size, <T as Config>::HeapSize>;

pub struct IntoU32<T, O>(sp_std::marker::PhantomData<(T, O)>);
impl<T: Get<O>, O: Into<u32>> Get<u32> for IntoU32<T, O> {
	fn get() -> u32 {
		T::get().into()
	}
}

impl<T: Config> ServiceQueues for Pallet<T> {
	fn service_queues(weight_limit: Weight) -> Weight {
		// The maximum weight that processing a single message may take.
		let overweight_limit = weight_limit;
		let mut weight = WeightCounter::from_limit(weight_limit);
		log::debug!(
			target: LOG_TARGET,
			"ServiceQueues::service_queues with weight {} and overweight_limit {}",
			weight_limit,
			overweight_limit
		);

		let mut next = match Self::bump_service_head(&mut weight) {
			Some(h) => h,
			None => return weight.consumed,
		};
		// The last queue that did not make any progress.
		// The loop aborts as soon as it arrives at this queue again without making any progress
		// on other queues in between.
		let mut last_no_progress = None;

		loop {
			let (progressed, n) = Self::service_queue(next.clone(), &mut weight, overweight_limit);
			next = match n {
				Some(n) =>
					if !progressed && last_no_progress == Some(n.clone()) {
						break
					} else {
						last_no_progress = Some(next);
						n
					},
				None => break,
			}
		}
		weight.consumed
	}
}

impl<T: Config> EnqueueMessage<MessageOriginOf<T>> for Pallet<T> {
	type MaxMessageLen =
		MaxMessageLen<<T::MessageProcessor as ProcessMessage>::Origin, T::Size, T::HeapSize>;

	fn enqueue_message(
		message: BoundedSlice<u8, Self::MaxMessageLen>,
		origin: <T::MessageProcessor as ProcessMessage>::Origin,
	) {
		// the `truncate_from` is just for safety - it will never fail since the bound is the
		// maximum encoded length of the type.
		origin.using_encoded(|data| {
			Self::do_enqueue_message(&origin, message, BoundedSlice::truncate_from(data))
		})
	}

	fn enqueue_messages<'a>(
		messages: impl Iterator<Item = BoundedSlice<'a, u8, Self::MaxMessageLen>>,
		origin: <T::MessageProcessor as ProcessMessage>::Origin,
	) {
		origin.using_encoded(|data| {
			// the `truncate_from` is just for safety - it will never fail since the bound is the
			// maximum encoded length of the type.
			let origin_data = BoundedSlice::truncate_from(data);
			for message in messages {
				Self::do_enqueue_message(&origin, message, origin_data);
			}
		})
	}
}
