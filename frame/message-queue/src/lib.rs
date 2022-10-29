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

#[cfg(test)]
mod tests;
mod weights;

use codec::{Codec, Decode, Encode, FullCodec, MaxEncodedLen};
use frame_support::{pallet_prelude::*, BoundedSlice};
use frame_system::pallet_prelude::*;
pub use pallet::*;
use scale_info::TypeInfo;
use sp_arithmetic::traits::{BaseArithmetic, Unsigned};
use sp_runtime::{
	traits::{Hash, One, Zero},
	SaturatedConversion, Saturating,
};
use sp_std::{fmt::Debug, prelude::*, vec};
pub use weights::WeightInfo;

/// Type for identifying an overweight message.
type OverweightIndex = u64;
/// Type for identifying a page.
type PageIndex = u32;

/// Data encoded and prefixed to the encoded `MessageItem`.
#[derive(Encode, Decode, MaxEncodedLen)]
pub struct ItemHeader<Size> {
	/// The length of this item, not including the size of this header. The next item of the page
	/// follows immediately after the payload of this item.
	payload_len: Size,
	/// Whether this item has been processed.
	is_processed: bool,
}

/// A page of messages. Pages always contain at least one item.
#[derive(Clone, Encode, Decode, RuntimeDebugNoBound, Default, TypeInfo, MaxEncodedLen)]
#[scale_info(skip_type_params(HeapSize))]
#[codec(mel_bound(Size: MaxEncodedLen))]
pub struct Page<Size: Into<u32> + Debug, HeapSize: Get<Size>> {
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
		Size: BaseArithmetic + Unsigned + Copy + Into<u32> + Codec + MaxEncodedLen + Debug,
		HeapSize: Get<Size>,
	> Page<Size, HeapSize>
{
	fn from_message(message: &[u8], origin: &[u8]) -> Self {
		let len = ItemHeader::<Size>::max_encoded_len() + origin.len() + message.len();
		let mut heap = Vec::with_capacity(len);
		let payload_len: Size = (origin.len() + message.len()).saturated_into(); // TODO: bounded inputs for safety
		let h = ItemHeader { payload_len, is_processed: false };
		h.using_encoded(|d| heap.extend_from_slice(d));
		heap.extend_from_slice(origin);
		heap.extend_from_slice(message);
		Page {
			remaining: One::one(),
			first: Zero::zero(),
			last: Zero::zero(),
			heap: BoundedVec::truncate_from(heap),
		}
	}

	fn try_append_message(&mut self, message: &[u8], origin: &[u8]) -> Result<(), ()> {
		let pos = self.heap.len();
		let len = (ItemHeader::<Size>::max_encoded_len() + origin.len() + message.len()) as u32;
		let payload_len: Size = (origin.len() + message.len()).saturated_into(); // TODO: bounded inputs for safety
		let h = ItemHeader { payload_len, is_processed: false };
		let heap_size: u32 = HeapSize::get().into();
		if heap_size.saturating_sub(self.heap.len() as u32) < len {
			// Can't fit.
			return Err(())
		}

		let mut heap = sp_std::mem::replace(&mut self.heap, Default::default()).into_inner();
		h.using_encoded(|d| heap.extend_from_slice(d));
		heap.extend_from_slice(origin);
		heap.extend_from_slice(message);
		debug_assert!(heap.len() as u32 <= HeapSize::get().into(), "already checked size; qed");
		self.heap = BoundedVec::truncate_from(heap);
		self.last = pos.saturated_into();
		self.remaining.saturating_inc();
		Ok(())
	}

	fn peek_first(&self) -> Option<BoundedSlice<u8, IntoU32<HeapSize, Size>>> {
		if self.first > self.last {
			return None
		}
		let mut item_slice = &self.heap[(self.first.into() as usize)..];
		if let Ok(h) = ItemHeader::<Size>::decode(&mut item_slice) {
			let payload_len = h.payload_len.into();
			if payload_len <= item_slice.len() as u32 {
				// impossible to truncate since is sliced up from `self.heap: BoundedVec<u8,
				// HeapSize>`
				return Some(BoundedSlice::truncate_from(&item_slice[..(payload_len as usize)]))
			}
		}
		debug_assert!(false, "message-queue: heap corruption");
		None
	}

	/// Point `first` at the next message, marking the first as processed if `is_processed` is true.
	fn skip_first(&mut self, is_processed: bool) {
		let f = self.first.into() as usize;
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

	fn is_complete(&self) -> bool {
		self.remaining.is_zero()
	}
}

#[derive(Copy, Clone, Eq, PartialEq, Encode, Decode, TypeInfo, Debug)]
pub enum ProcessMessageError {
	/// The message data format is unknown (e.g. unrecognised header)
	BadFormat,
	/// The message data is bad (e.g. decoding returns an error).
	Corrupt,
	/// The message format is unsupported (e.g. old XCM version).
	Unsupported,
	/// Message processing was not attempted because it was not certain that the weight limit
	/// would be respected. The parameter gives the maximum weight which the message could take
	/// to process.
	Overweight(Weight),
}

pub trait ProcessMessage {
	/// The transport from where a message originates.
	type Origin: FullCodec + MaxEncodedLen + Clone + Eq + PartialEq + TypeInfo + sp_std::fmt::Debug;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	fn process_message(
		message: &[u8],
		origin: Self::Origin,
		weight_limit: Weight,
	) -> Result<(bool, Weight), ProcessMessageError>;
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
			+ TypeInfo;

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
		Discarded { hash: T::Hash },
		/// Message discarded due to an error in the `MessageProcessor` (usually a format error).
		ProcessingFailed { hash: T::Hash, origin: MessageOriginOf<T>, error: ProcessMessageError },
		/// Message is processed.
		Processed { hash: T::Hash, origin: MessageOriginOf<T>, weight_used: Weight, success: bool },
		/// Message placed in overweight queue.
		Overweight { hash: T::Hash, origin: MessageOriginOf<T>, index: OverweightIndex },
	}

	#[pallet::error]
	pub enum Error<T> {
		/// Page is not reapable because it has items remaining to be processed and is not old
		/// enough.
		NotReapable,
		/// Page to be reaped does not exist.
		NoPage,
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
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(0)]
		pub fn send(origin: OriginFor<T>) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			Ok(())
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
		#[pallet::weight(0)]
		pub fn execute_overweight(
			origin: OriginFor<T>,
			message_origin: MessageOriginOf<T>,
			page: PageIndex,
			index: T::Size,
			weight_limit: Weight,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;

			Ok(())
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
				debug_assert!(false, "`ServiceHead` must be some if there was a ready queue");
			}
		}
	}

	fn bump_service_head() -> Option<MessageOriginOf<T>> {
		if let Some(head) = ServiceHead::<T>::get() {
			let mut head_book_state = BookStateOf::<T>::get(&head);
			if let Some(head_neighbours) = head_book_state.ready_neighbours.take() {
				ServiceHead::<T>::put(&head_neighbours.next);
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
					debug_assert!(false, "Corruption: referenced page doesn't exist.");
					return
				},
			};
			if let Ok(_) = page.try_append_message(&message[..], &origin_data[..]) {
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
			Page::from_message(&message[..], &origin_data[..]),
		);
		BookStateOf::<T>::insert(&origin, book_state);
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

		Ok(())
	}

	/// Execute any messages remaining to be processed in the queue of `origin`, using up to
	/// `weight_limit` to do so. Any messages which would take more than `overweight_limit` to
	/// execute are deemed overweight and ignored.
	fn service_queue(
		origin: MessageOriginOf<T>,
		weight_limit: Weight,
		overweight_limit: Weight,
	) -> (Weight, Option<MessageOriginOf<T>>) {
		let mut processed = 0;
		let mut weight_left = weight_limit;
		let mut book_state = BookStateOf::<T>::get(&origin);
		while book_state.end > book_state.begin {
			let page_index = book_state.begin;
			// TODO: Check `weight_left` and bail before doing this storage read.
			let mut page = match Pages::<T>::get(&origin, page_index) {
				Some(p) => p,
				None => {
					debug_assert!(false, "message-queue: referenced page not found");
					break
				},
			};

			let bail = loop {
				let mut message = &match page.peek_first() {
					Some(m) => m,
					None => break false,
				}[..];

				if weight_left.any_lte(Weight::zero()) {
					break true
				}

				let is_processed = match MessageOriginOf::<T>::decode(&mut message) {
					Ok(origin) => {
						let hash = T::Hashing::hash(message);
						use ProcessMessageError::Overweight;
						match T::MessageProcessor::process_message(
							message,
							origin.clone(),
							weight_left,
						) {
							Err(Overweight(w)) if processed == 0 || w.any_gt(overweight_limit) => {
								// Permanently overweight.
								Self::deposit_event(Event::<T>::Overweight {
									hash,
									origin,
									index: 0,
								}); // TODO page + index
								false
							},
							Err(Overweight(_)) => {
								// Temporarily overweight - save progress and stop processing this
								// queue.
								break true
							},
							Err(error) => {
								// Permanent error - drop
								Self::deposit_event(Event::<T>::ProcessingFailed {
									hash,
									origin,
									error,
								});
								true
							},
							Ok((success, weight_used)) => {
								// Success
								processed.saturating_inc();
								weight_left = weight_left.saturating_sub(weight_used);
								let event =
									Event::<T>::Processed { hash, origin, weight_used, success };
								Self::deposit_event(event);
								true
							},
						}
					},
					Err(_) => {
						let hash = T::Hashing::hash(message);
						Self::deposit_event(Event::<T>::Discarded { hash });
						false
					},
				};
				page.skip_first(is_processed);
			};

			if page.is_complete() {
				debug_assert!(!bail, "we never bail if a page became complete");
				Pages::<T>::remove(&origin, page_index);
				debug_assert!(book_state.count > 0, "completing a page implies there are pages");
				book_state.count.saturating_dec();
			} else {
				Pages::<T>::insert(&origin, page_index, page);
			}

			if bail {
				break
			}
			book_state.begin.saturating_inc();
		}
		let next_ready = book_state.ready_neighbours.as_ref().map(|x| x.next.clone());
		if book_state.begin >= book_state.end && processed > 0 {
			// No longer ready - unknit.
			if let Some(neighbours) = book_state.ready_neighbours.take() {
				Self::ready_ring_unknit(&origin, neighbours);
			} else {
				debug_assert!(false, "Freshly processed queue must have been ready");
			}
		}
		BookStateOf::<T>::insert(&origin, &book_state);
		(weight_limit.saturating_sub(weight_left), next_ready)
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

pub struct IntoU32<T, O>(sp_std::marker::PhantomData<(T, O)>);
impl<T: Get<O>, O: Into<u32>> Get<u32> for IntoU32<T, O> {
	fn get() -> u32 {
		T::get().into()
	}
}

pub trait ServiceQueues {
	/// Service all message queues in some fair manner.
	///
	/// - `weight_limit`: The maximum amount of dynamic weight that this call can use.
	///
	/// Returns the dynamic weight used by this call; is never greater than `weight_limit`.
	fn service_queues(weight_limit: Weight) -> Weight;
}

impl<T: Config> ServiceQueues for Pallet<T> {
	fn service_queues(weight_limit: Weight) -> Weight {
		let max_weight = weight_limit.saturating_mul(3).saturating_div(4);
		let mut weight_used = Weight::zero();
		let mut next = match Self::bump_service_head() {
			Some(h) => h,
			None => return weight_used,
		};

		loop {
			let left = weight_limit - weight_used;
			if left.any_lte(Weight::zero()) {
				break
			}
			// Before servicing, bump `ServiceHead` onto the next item.
			let (used, n) = Self::service_queue(next, left, max_weight);
			weight_used.saturating_accrue(used);
			next = match n {
				Some(n) => n,
				None => break,
			}
		}
		weight_used
	}
}

pub trait EnqueueMessage<Origin: MaxEncodedLen> {
	type MaxMessageLen: Get<u32>;

	/// Enqueue a single `message` from a specific `origin`.
	///
	/// Infallible.
	fn enqueue_message(message: BoundedSlice<u8, Self::MaxMessageLen>, origin: Origin);

	/// Enqueue multiple `messages` from a specific `origin`.
	///
	/// If no `message.len()` is greater than `HEAP_SIZE - Origin::max_encoded_len()`, then this
	/// is guaranteed to succeed. In the case of `Err`, no messages are queued.
	fn enqueue_messages<'a>(
		messages: impl Iterator<Item = BoundedSlice<'a, u8, Self::MaxMessageLen>>,
		origin: Origin,
	);

	// TODO: consider: `fn enqueue_mqc_page(page: &[u8], origin: Origin);`
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
