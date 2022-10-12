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

use codec::{Decode, Encode, Codec, MaxEncodedLen};
use frame_support::{parameter_types, BoundedSlice};
use scale_info::TypeInfo;
use sp_std::{prelude::*, vec};
use sp_runtime::Saturating;
use frame_support::pallet_prelude::*;
use frame_system::pallet_prelude::*;
pub use pallet::*;
pub use weights::WeightInfo;

/// Type for identifying an overweight message.
type OverweightIndex = u64;
/// Type for identifying a page.
type PageIndex = u32;
/// Type for representing the size of an offset into a page heap.
type Offset = u16;
/// Type for representing the size of an individual encoded `MessageItem`.
type Size = u16;
/// Maximum size of a page's heap.
const HEAP_SIZE: u32 = 1u32 << 16;

parameter_types! {
	pub const HeapSize: u32 = HEAP_SIZE;
}

/// Data encoded and prefixed to the encoded `MessageItem`.
#[derive(Encode, Decode, MaxEncodedLen)]
pub struct ItemHeader {
	/// The length of this item, not including the size of this header. The next item of the page
	/// follows immediately after the payload of this item.
	payload_len: Size,
	/// Whether this item has been processed.
	is_processed: bool,
}

/// A page of messages. Pages always contain at least one item.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, Default)]
pub struct Page {
	/// Messages remaining to be processed; this includes overweight messages which have been
	/// skipped.
	remaining: Size,
	/// The heap-offset of the header of the first message item in this page which is ready for
	/// processing.
	first: Offset,
	/// The heap-offset of the header of the last message item in this page.
	last: Offset,
	/// The heap. If `self.offset == self.heap.len()` then the page is empty and should be deleted.
	heap: BoundedVec<u8, HeapSize>,
}

impl Page {
	fn from_message(message: &[u8], origin: &[u8]) -> Self {
		let len = ItemHeader::max_encoded_len() + origin.len() + message.len();
		let mut heap = Vec::with_capacity(len);
		let payload_len = (origin.len() + message.len()) as Size;// TODO: bounded inputs for safety
		let h = ItemHeader { payload_len, is_processed: false };
		h.using_encoded(|d| heap.extend_from_slice(d));
		heap.extend_from_slice(origin);
		heap.extend_from_slice(message);
		Page {
			remaining: 1,
			first: 0,
			last: 0,
			heap: BoundedVec::truncate_from(heap),
		}
	}

	fn try_append_message(&mut self, message: &[u8], origin: &[u8]) -> Result<(), ()> {
		let pos = self.heap.len();
		let len = ItemHeader::max_encoded_len() + origin.len() + message.len();
		let payload_len = (origin.len() + message.len()) as Size;// TODO: bounded inputs for safety
		let h = ItemHeader { payload_len, is_processed: false };
		if (HEAP_SIZE as usize).saturating_sub(self.heap.len()) < len {
			// Can't fit.
			return Err(())
		}

		let mut heap = sp_std::mem::replace(&mut self.heap, Default::default()).into_inner();
		h.using_encoded(|d| heap.extend_from_slice(d));
		heap.extend_from_slice(origin);
		heap.extend_from_slice(message);
		debug_assert!((heap.len() as u32) < HEAP_SIZE, "already checked size; qed");
		self.heap = BoundedVec::truncate_from(heap);
		self.last = pos as Offset;
		self.remaining.saturating_inc();
		Ok(())
	}

	fn peek_first(&self) -> Option<BoundedSlice<u8, HeapSize>> {
		if self.first >= self.last {
			return None
		}
		let mut item_slice = &self.heap[self.first as usize..];
		if let Ok(h) = ItemHeader::decode(&mut item_slice) {
			let payload_len = h.payload_len as usize;
			if payload_len <= item_slice.len() {
				// impossible to truncate since is sliced up from `self.heap: BoundedVec<u8, HeapSize>`
				return Some(BoundedSlice::truncate_from(&item_slice[..payload_len]))
			}
		}
		debug_assert!(false, "message-queue: heap corruption");
		None
	}

	/// Point `first` at the next message, marking the first as processed if `is_processed` is true.
	fn skip_first(&mut self, is_processed: bool) {
		let f = self.first as usize;
		if let Ok(mut h) = ItemHeader::decode(&mut &self.heap[f..]) {
			if is_processed && !h.is_processed {
				h.is_processed = true;
				h.using_encoded(|d|
					self.heap[f..f + d.len()].copy_from_slice(d)
				);
				self.remaining.saturating_dec();
			}
			self.first.saturating_accrue(ItemHeader::max_encoded_len() as Size + h.payload_len);
		}
	}

	fn is_complete(&self) -> bool {
		self.remaining == 0
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
	type Origin: Codec + MaxEncodedLen + Clone + Eq + PartialEq + TypeInfo + sp_std::fmt::Debug;

	/// Process the given message, using no more than `weight_limit` in weight to do so.
	fn process_message(message: &[u8], origin: Self::Origin, weight_limit: Weight) -> Result<(bool, Weight), ProcessMessageError>;
}

#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, Default)]
pub struct BookState {
	/// The first page with some items to be processed in it. If this is `>= end`, then there are
	/// no pages with items to be processing in them.
	begin: PageIndex,
	/// One more than the last page with some items to be processed in it.
	end: PageIndex,
	/// The number of pages stored at present.
	count: PageIndex,
	/// The earliest page still in storage. If this is `>= end`, then there are
	/// no pages in storage. Pages up to `head` are reapable if they have a `remaining`
	/// field of zero or if `head - page_number` is sufficiently large compared to
	/// `count - (end - begin)`.
	historical_head: PageIndex,
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
		/// Dummy.
		Dummy,
	}

	/// The index of the first and last (non-empty) pages.
	#[pallet::storage]
	pub(super) type BookStateOf<T: Config> = StorageValue<_, BookState, ValueQuery>;

	/// The lowest known unused page index.
	#[pallet::storage]
	pub(super) type NextPage<T: Config> = StorageValue<_, PageIndex, ValueQuery>;

	/// The map of page indices to pages.
	#[pallet::storage]
	pub(super) type Pages<T: Config> = StorageMap<_, Blake2_256, PageIndex, Page, OptionQuery>;

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
		pub fn send(
			origin: OriginFor<T>,
		) -> DispatchResult {
			let _ = ensure_signed(origin)?;
			Ok(())
		}
	}
}

impl<T: Config> Pallet<T> {
	fn new_page() -> PageIndex {
		let page = NextPage::<T>::get();
		NextPage::<T>::put(page + 1);
		page
	}

	fn do_enqueue_message(
		message: BoundedSlice<u8, MaxMessageLenOf<T>>,
		origin: BoundedSlice<u8, MaxOriginLenOf<T>>,
	) {
		let mut book_state = BookStateOf::<T>::get();
		if book_state.end > book_state.begin {
			// Already have a page in progress - attempt to append.
			let last = book_state.end - 1;
			let mut page = match Pages::<T>::get(last) {
				Some(p) => p,
				None => {
					debug_assert!(false, "Corruption: referenced page doesn't exist.");
					return
				}
			};
			if let Ok(_) = page.try_append_message(&message[..], &origin[..]) {
				Pages::<T>::insert(last, &page);
				return
			}
		}
		// No room on the page or no page - link in a new page.
		book_state.end.saturating_inc();
		Pages::<T>::insert(book_state.end - 1, Page::from_message(&message[..], &origin[..]));
		BookStateOf::<T>::put(book_state);
	}
/*
	/// Service the message queue.
	///
	/// - `weight_limit`: The maximum amount of dynamic weight that this call can use.
	///
	/// Returns the dynamic weight used by this call; is never greater than `weight_limit`.
	fn service_queue(weight_limit: Weight) -> Weight {
		let mut processed = 0;
		let max_weight = weight_limit.saturating_mul(3).saturating_div(4);
		let mut weight_left = weight_limit;
		let mut maybe_book_state = BookStateOf::<T>::get();
		while let Some(ref mut book_state) = maybe_book_state {
			let page_index = book_state.head;
			// TODO: Check `weight_left` and bail before doing this storage read.
			let mut page = Pages::<T>::get(page_index);

			let bail = loop {
				let mut message = page.peek_first();

				let was_processed = match MessageOriginOf::<T>::decode(&mut message) {
					Ok(origin) => {
						let hash = T::Hashing::hash_of(message);
						use ProcessMessageError::Overweight;
						match T::MessageProcessor::process_message(message, origin.clone(), weight_left) {
							Err(Overweight(w)) if processed == 0 || w.any_gte(max_weight) => {
								// Permanently overweight - place into overweight queue.
								// TODO: record the weight used.
								let index = 0;//Self::insert_overweight(origin, message);
								Self::deposit_event(Event::<T>::Overweight { hash, origin, index });
								false
							},
							Err(Overweight(_)) => {
								// Temporarily overweight - save progress and stop processing this queue.
								Pages::<T>::insert(page_index, page);
								break true
							}
							Err(error) => {
								// Permanent error - drop
								Self::deposit_event(Event::<T>::ProcessingFailed { hash, origin, error });
								true
							},
							Ok((success, weight_used)) => {
								// Success
								weight_left.saturating_reduce(weight_used);
								let event = Event::<T>::Processed { hash, origin, weight_used, success };
								Self::deposit_event(event);
								true
							},
						}
					},
					Err(_) => {
						let hash = T::Hashing::hash_of(message);
						Self::deposit_event(Event::<T>::Discarded { hash });
					}
				};

				page = match page.without_first(was_processed) {
					Ok(p) => p,
					Err(maybe_next_page) => {
						Pages::<T>::remove(page_index);
						if let Some(next_page) = maybe_next_page {
							book_state.head = next_page;
							break false
						} else {
							BookStateOf::<T>::kill();
							break true
						}
					},
				};
			};
			if bail {
				break
			}
		}
		BookStateOf::<T>::set(maybe_book_state);
		weight_limit.saturating_sub(weight_left)
	}
	*/
}

pub struct MaxEncodedLenOf<T>(sp_std::marker::PhantomData<T>);
impl<T: MaxEncodedLen> Get<u32> for MaxEncodedLenOf<T> {
	fn get() -> u32 {
		T::max_encoded_len() as u32
	}
}

pub struct MaxMessageLen<Origin, HeapSize>(sp_std::marker::PhantomData<(Origin, HeapSize)>);
impl<Origin: MaxEncodedLen, HeapSize: Get<u32>> Get<u32> for MaxMessageLen<Origin, HeapSize> {
	fn get() -> u32 {
		HeapSize::get()
			.saturating_sub(Origin::max_encoded_len() as u32)
			.saturating_sub(ItemHeader::max_encoded_len() as u32)
	}
}

pub type MaxMessageLenOf<T> = MaxMessageLen<MessageOriginOf<T>, HeapSize>;
pub type MaxOriginLenOf<T> = MaxEncodedLenOf<MessageOriginOf<T>>;
pub type MessageOriginOf<T> = <<T as Config>::MessageProcessor as ProcessMessage>::Origin;

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
	fn enqueue_messages(messages: &[BoundedSlice<u8, Self::MaxMessageLen>], origin: Origin);

	// TODO: consider: `fn enqueue_mqc_page(page: &[u8], origin: Origin);`
}

impl<T: Config> EnqueueMessage<MessageOriginOf<T>> for Pallet<T> {
	type MaxMessageLen = MaxMessageLen<<T::MessageProcessor as ProcessMessage>::Origin, HeapSize>;

	fn enqueue_message(message: BoundedSlice<u8, Self::MaxMessageLen>, origin: <T::MessageProcessor as ProcessMessage>::Origin) {
		// the `truncate_from` is just for safety - it will never fail since the bound is the
		// maximum encoded length of the type.
		origin.using_encoded(|data| Self::do_enqueue_message(message, BoundedSlice::truncate_from(data)))
	}

	fn enqueue_messages(messages: &[BoundedSlice<u8, Self::MaxMessageLen>], origin: <T::MessageProcessor as ProcessMessage>::Origin) {
		origin.using_encoded(|data| {
			// the `truncate_from` is just for safety - it will never fail since the bound is the
			// maximum encoded length of the type.
			let origin_data = BoundedSlice::truncate_from(data);
			for &message in messages.iter() {
				Self::do_enqueue_message(message, origin_data);
			}
		})
	}
}
