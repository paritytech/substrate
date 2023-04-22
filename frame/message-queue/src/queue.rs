use frame_support::pallet_macros::*;

/// Data encoded and prefixed to the encoded `MessageItem`.
#[derive(Encode, Decode, PartialEq, MaxEncodedLen, Debug)]
pub struct ItemHeader<Size> {
	/// The length of this item, not including the size of this header. The next item of the page
	/// follows immediately after the payload of this item.
	payload_len: Size,
	/// Whether this item has been processed.
	is_processed: bool,
}


/// A single link in the double-linked Ready Ring list.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebug, PartialEq)]
pub struct Neighbours<MessageOrigin> {
	/// The previous queue.
	prev: MessageOrigin,
	/// The next queue.
	next: MessageOrigin,
}

/// The state of a queue as represented by a book of its pages.
///
/// Each queue has exactly one book which holds all of its pages. All pages of a book combined
/// contain all of the messages of its queue; hence the name *Book*.
/// Books can be chained together in a double-linked fashion through their `ready_neighbours` field.
#[derive(Clone, Encode, Decode, MaxEncodedLen, TypeInfo, RuntimeDebug)]
pub struct BookState<MessageOrigin> {
	/// The first page with some items to be processed in it. If this is `>= end`, then there are
	/// no pages with items to be processing in them.
	begin: PageIndex,
	/// One more than the last page with some items to be processed in it.
	end: PageIndex,
	/// The number of pages stored at present.
	///
	/// This might be larger than `end-begin`, because we keep pages with unprocessed overweight
	/// messages outside of the end/begin window.
	count: PageIndex,
	/// If this book has any ready pages, then this will be `Some` with the previous and next
	/// neighbours. This wraps around.
	ready_neighbours: Option<Neighbours<MessageOrigin>>,
	/// The number of unprocessed messages stored at present.
	message_count: u64,
	/// The total size of all unprocessed messages stored at present.
	size: u64,
}

impl<MessageOrigin> Default for BookState<MessageOrigin> {
	fn default() -> Self {
		Self { begin: 0, end: 0, count: 0, ready_neighbours: None, message_count: 0, size: 0 }
	}
}

/// Handler code for when the items in a queue change.
pub trait OnQueueChanged<Id> {
	/// Note that the queue `id` now has `item_count` items in it, taking up `items_size` bytes.
	fn on_queue_changed(id: Id, items_count: u64, items_size: u64);
}

impl<Id> OnQueueChanged<Id> for () {
	fn on_queue_changed(_: Id, _: u64, _: u64) {}
}

#[export_section]
mod queue {
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
		OverweightEnqueued {
			hash: T::Hash,
			origin: MessageOriginOf<T>,
			page_index: PageIndex,
			message_index: T::Size,
		},
		/// This page was reaped.
		PageReaped { origin: MessageOriginOf<T>, index: PageIndex },
	}


	#[pallet::error]
	pub enum Error<T> {
		/// Page is not reapable because it has items remaining to be processed and is not old
		/// enough.
		NotReapable,
		/// Page to be reaped does not exist.
		NoPage,
		/// The referenced message could not be found.
		NoMessage,
		/// The message was already processed and cannot be processed again.
		AlreadyProcessed,
		/// The message is queued for future execution.
		Queued,
		/// There is temporarily not enough weight to continue servicing messages.
		InsufficientWeight,
		/// This message is temporarily unprocessable.
		///
		/// Such errors are expected, but not guaranteed, to resolve themselves eventually through
		/// retrying.
		TemporarilyUnprocessable,
	}
}