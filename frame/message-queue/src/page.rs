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
	/// The size of all remaining messages to be processed.
	///
	/// Includes overweight messages outside of the `first` to `last` window.
	remaining_size: Size,
	/// The number of items before the `first` item in this page.
	first_index: Size,
	/// The heap-offset of the header of the first message item in this page which is ready for
	/// processing.
	first: Size,
	/// The heap-offset of the header of the last message item in this page.
	last: Size,
	/// The heap. If `self.offset == self.heap.len()` then the page is empty and should be deleted.
	heap: BoundedVec<u8, IntoU32<HeapSize, Size>>,
}

/// Type for identifying a page.
type PageIndex = u32;

impl<
		Size: BaseArithmetic + Unsigned + Copy + Into<u32> + Codec + MaxEncodedLen + Debug + Default,
		HeapSize: Get<Size>,
	> Page<Size, HeapSize>
{
	/// Create a [`Page`] from one unprocessed message.
	fn from_message<T: Config>(message: BoundedSlice<u8, MaxMessageLenOf<T>>) -> Self {
		let payload_len = message.len();
		let data_len = ItemHeader::<Size>::max_encoded_len().saturating_add(payload_len);
		let payload_len = payload_len.saturated_into();
		let header = ItemHeader::<Size> { payload_len, is_processed: false };

		let mut heap = Vec::with_capacity(data_len);
		header.using_encoded(|h| heap.extend_from_slice(h));
		heap.extend_from_slice(message.deref());

		Page {
			remaining: One::one(),
			remaining_size: payload_len,
			first_index: Zero::zero(),
			first: Zero::zero(),
			last: Zero::zero(),
			heap: BoundedVec::defensive_truncate_from(heap),
		}
	}

	/// Try to append one message to a page.
	fn try_append_message<T: Config>(
		&mut self,
		message: BoundedSlice<u8, MaxMessageLenOf<T>>,
	) -> Result<(), ()> {
		let pos = self.heap.len();
		let payload_len = message.len();
		let data_len = ItemHeader::<Size>::max_encoded_len().saturating_add(payload_len);
		let payload_len = payload_len.saturated_into();
		let header = ItemHeader::<Size> { payload_len, is_processed: false };
		let heap_size: u32 = HeapSize::get().into();
		if (heap_size as usize).saturating_sub(self.heap.len()) < data_len {
			// Can't fit.
			return Err(())
		}

		let mut heap = sp_std::mem::take(&mut self.heap).into_inner();
		header.using_encoded(|h| heap.extend_from_slice(h));
		heap.extend_from_slice(message.deref());
		self.heap = BoundedVec::defensive_truncate_from(heap);
		self.last = pos.saturated_into();
		self.remaining.saturating_inc();
		self.remaining_size.saturating_accrue(payload_len);
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
				self.remaining_size.saturating_reduce(h.payload_len);
			}
			self.first
				.saturating_accrue(ItemHeader::<Size>::max_encoded_len().saturated_into());
			self.first.saturating_accrue(h.payload_len);
			self.first_index.saturating_inc();
		}
	}

	/// Return the message with index `index` in the form of `(position, processed, message)`.
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
	///
	/// Does nothing if no [`ItemHeader`] could be decoded at the given position.
	fn note_processed_at_pos(&mut self, pos: usize) {
		if let Ok(mut h) = ItemHeader::<Size>::decode(&mut &self.heap[pos..]) {
			if !h.is_processed {
				h.is_processed = true;
				h.using_encoded(|d| self.heap[pos..pos + d.len()].copy_from_slice(d));
				self.remaining.saturating_dec();
				self.remaining_size.saturating_reduce(h.payload_len);
			}
		}
	}

	/// Returns whether the page is *complete* which means that no messages remain.
	fn is_complete(&self) -> bool {
		self.remaining.is_zero()
	}
}