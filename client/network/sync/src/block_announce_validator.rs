// This file is part of Substrate.

// Copyright (C) 2017-2023 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! `BlockAnnounceValidator` is responsible for async validation of block announcements.

use event_listener::{Event, EventListener};
use futures::{stream::FuturesUnordered, Future, FutureExt, Stream, StreamExt};
use libp2p::PeerId;
use log::{debug, error, trace, warn};
use sc_network_common::sync::message::BlockAnnounce;
use sp_consensus::block_validation::Validation;
use sp_runtime::traits::{Block as BlockT, Header, Zero};
use std::{
	collections::{hash_map::Entry, HashMap},
	pin::Pin,
	task::{Context, Poll},
};

/// Log target for this file.
const LOG_TARGET: &str = "sync";

/// Maximum number of concurrent block announce validations.
///
/// If the queue reaches the maximum, we drop any new block
/// announcements.
const MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS: usize = 256;

/// Maximum number of concurrent block announce validations per peer.
///
/// See [`MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS`] for more information.
const MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS_PER_PEER: usize = 4;

/// Item that yields [`Stream`] implementation of [`BlockAnnounceValidator`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum BlockAnnounceValidationResult<H> {
	/// The announcement failed at validation.
	///
	/// The peer reputation should be decreased.
	Failure {
		/// The id of the peer that send us the announcement.
		peer_id: PeerId,
		/// Should the peer be disconnected?
		disconnect: bool,
	},
	/// The announcement was validated successfully and should be passed to [`crate::ChainSync`].
	Process {
		/// The id of the peer that send us the announcement.
		peer_id: PeerId,
		/// Was this their new best block?
		is_new_best: bool,
		/// The announcement.
		announce: BlockAnnounce<H>,
	},
	/// The block announcement should be skipped.
	Skip {
		/// The id of the peer that send us the announcement.
		peer_id: PeerId,
	},
}

impl<H> BlockAnnounceValidationResult<H> {
	fn peer_id(&self) -> &PeerId {
		match self {
			BlockAnnounceValidationResult::Failure { peer_id, .. } |
			BlockAnnounceValidationResult::Process { peer_id, .. } |
			BlockAnnounceValidationResult::Skip { peer_id } => peer_id,
		}
	}
}

/// Result of [`BlockAnnounceValidator::allocate_slot_for_block_announce_validation`].
enum AllocateSlotForBlockAnnounceValidation {
	/// Success, there is a slot for the block announce validation.
	Allocated,
	/// We reached the total maximum number of validation slots.
	TotalMaximumSlotsReached,
	/// We reached the maximum number of validation slots for the given peer.
	MaximumPeerSlotsReached,
}

pub(crate) struct BlockAnnounceValidator<B: BlockT> {
	/// A type to check incoming block announcements.
	validator: Box<dyn sp_consensus::block_validation::BlockAnnounceValidator<B> + Send>,
	/// All block announcements that are currently being validated.
	validations: FuturesUnordered<
		Pin<Box<dyn Future<Output = BlockAnnounceValidationResult<B::Header>> + Send>>,
	>,
	/// Number of concurrent block announce validations per peer.
	validations_per_peer: HashMap<PeerId, usize>,
	/// Wake-up event when new validations are pushed.
	event: Event,
	/// Listener for wake-up events in [`Stream::poll_next`] implementation.
	event_listener: Option<EventListener>,
}

impl<B: BlockT> BlockAnnounceValidator<B> {
	pub(crate) fn new(
		validator: Box<dyn sp_consensus::block_validation::BlockAnnounceValidator<B> + Send>,
	) -> Self {
		Self {
			validator,
			validations: Default::default(),
			validations_per_peer: Default::default(),
			event: Event::new(),
			event_listener: None,
		}
	}

	/// Push a block announce validation.
	pub(crate) fn push_block_announce_validation(
		&mut self,
		peer_id: PeerId,
		hash: B::Hash,
		announce: BlockAnnounce<B::Header>,
		is_best: bool,
	) {
		let header = &announce.header;
		let number = *header.number();
		debug!(
			target: LOG_TARGET,
			"Pre-validating received block announcement {:?} with number {:?} from {}",
			hash,
			number,
			peer_id,
		);

		if number.is_zero() {
			warn!(
				target: LOG_TARGET,
				"💔 Ignored genesis block (#0) announcement from {}: {}",
				peer_id,
				hash,
			);
			return
		}

		// Try to allocate a slot for this block announce validation.
		match self.allocate_slot_for_block_announce_validation(&peer_id) {
			AllocateSlotForBlockAnnounceValidation::Allocated => {},
			AllocateSlotForBlockAnnounceValidation::TotalMaximumSlotsReached => {
				warn!(
					target: LOG_TARGET,
					"💔 Ignored block (#{} -- {}) announcement from {} because all validation slots are occupied.",
					number,
					hash,
					peer_id,
				);
				return
			},
			AllocateSlotForBlockAnnounceValidation::MaximumPeerSlotsReached => {
				warn!(
					target: LOG_TARGET,
					"💔 Ignored block (#{} -- {}) announcement from {} because all validation slots for this peer are occupied.",
					number,
					hash,
					peer_id,
				);
				return
			},
		}

		// Let external validator check the block announcement.
		let assoc_data = announce.data.as_ref().map_or(&[][..], |v| v.as_slice());
		let future = self.validator.validate(header, assoc_data);

		self.validations.push(
			async move {
				match future.await {
					Ok(Validation::Success { is_new_best }) => {
						let is_new_best = is_new_best || is_best;

						trace!(
							target: LOG_TARGET,
							"Block announcement validated successfully: from {}: {:?}. Local best: {}.",
							peer_id,
							announce.summary(),
							is_new_best,
						);

						BlockAnnounceValidationResult::Process { is_new_best, announce, peer_id }
					},
					Ok(Validation::Failure { disconnect }) => {
						debug!(
							target: LOG_TARGET,
							"Block announcement validation failed: from {}, block {:?}. Disconnect: {}.",
							peer_id,
							hash,
							disconnect,
						);

						BlockAnnounceValidationResult::Failure { peer_id, disconnect }
					},
					Err(e) => {
						debug!(
							target: LOG_TARGET,
							"💔 Ignoring block announcement validation from {} of block {:?} due to internal error: {}.",
							peer_id,
							hash,
							e,
						);

						BlockAnnounceValidationResult::Skip { peer_id }
					},
				}
			}
			.boxed(),
		);

		// Make sure [`Stream::poll_next`] is woken up.
		self.event.notify(1);
	}

	/// Checks if there is a slot for a block announce validation.
	///
	/// The total number and the number per peer of concurrent block announce validations
	/// is capped.
	///
	/// Returns [`AllocateSlotForBlockAnnounceValidation`] to inform about the result.
	///
	/// # Note
	///
	/// It is *required* to call [`Self::deallocate_slot_for_block_announce_validation`] when the
	/// validation is finished to clear the slot.
	fn allocate_slot_for_block_announce_validation(
		&mut self,
		peer_id: &PeerId,
	) -> AllocateSlotForBlockAnnounceValidation {
		if self.validations.len() >= MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS {
			return AllocateSlotForBlockAnnounceValidation::TotalMaximumSlotsReached
		}

		match self.validations_per_peer.entry(*peer_id) {
			Entry::Vacant(entry) => {
				entry.insert(1);
				AllocateSlotForBlockAnnounceValidation::Allocated
			},
			Entry::Occupied(mut entry) => {
				if *entry.get() < MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS_PER_PEER {
					*entry.get_mut() += 1;
					AllocateSlotForBlockAnnounceValidation::Allocated
				} else {
					AllocateSlotForBlockAnnounceValidation::MaximumPeerSlotsReached
				}
			},
		}
	}

	/// Should be called when a block announce validation is finished, to update the slots
	/// of the peer that send the block announce.
	fn deallocate_slot_for_block_announce_validation(&mut self, peer_id: &PeerId) {
		match self.validations_per_peer.entry(*peer_id) {
			Entry::Vacant(_) => {
				error!(
					target: LOG_TARGET,
					"💔 Block announcement validation from peer {} finished for that no slot was allocated!",
					peer_id,
				);
			},
			Entry::Occupied(mut entry) => match entry.get().checked_sub(1) {
				Some(value) =>
					if value == 0 {
						entry.remove();
					} else {
						*entry.get_mut() = value;
					},
				None => {
					entry.remove();

					error!(
						target: LOG_TARGET,
						"Invalid (zero) block announce validation slot counter for peer {peer_id}.",
					);
					debug_assert!(
						false,
						"Invalid (zero) block announce validation slot counter for peer {peer_id}.",
					);
				},
			},
		}
	}
}

impl<B: BlockT> Stream for BlockAnnounceValidator<B> {
	type Item = BlockAnnounceValidationResult<B::Header>;

	/// Poll for finished block announce validations. The stream never terminates.
	fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
		// Note: the wake-up code below is modeled after `async-channel`.
		// See https://github.com/smol-rs/async-channel/blob/4cae9cb0cbbd7c3c0518438e03a01e312b303e59/src/lib.rs#L787-L825
		loop {
			// Wait for wake-up event if we are in a waiting state after `self.validations`
			// was deplenished.
			if let Some(listener) = self.event_listener.as_mut() {
				match listener.poll_unpin(cx) {
					Poll::Ready(()) => self.event_listener = None,
					Poll::Pending => return Poll::Pending,
				}
			}

			loop {
				match self.validations.poll_next_unpin(cx) {
					Poll::Ready(Some(validation)) => {
						self.event_listener = None;

						self.deallocate_slot_for_block_announce_validation(validation.peer_id());

						return Poll::Ready(Some(validation))
					},
					Poll::Ready(None) => {},
					Poll::Pending => return Poll::Pending,
				}

				// `self.validations` was deplenished, start/continue waiting for a wake-up event.
				match self.event_listener {
					Some(_) => {
						// Go back to the outer loop to wait for a wake-up event.
						break
					},
					None => {
						// Create listener and go polling `self.validations` again in case it was
						// populated just before the listener was created.
						self.event_listener = Some(self.event.listen());
					},
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::block_announce_validator::AllocateSlotForBlockAnnounceValidation;
	use futures::{future::BoxFuture, stream::FuturesUnordered, FutureExt, StreamExt};
	use libp2p::PeerId;
	use sp_consensus::block_validation::DefaultBlockAnnounceValidator;
	use std::task::Poll;
	use substrate_test_runtime_client::runtime::Block;

	/// `Stream` implementation for `BlockAnnounceValidator` relies on the undocumented
	/// feature that `FuturesUnordered` can be polled and repeatedly yield
	/// `Poll::Ready(None)` before any futures were added into it.
	#[tokio::test]
	async fn empty_futures_unordered_can_be_polled() {
		let mut unordered = FuturesUnordered::<BoxFuture<()>>::default();

		futures::future::poll_fn(|cx| {
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));

			Poll::Ready(())
		})
		.await;
	}

	/// `Stream` implementation for `BlockAnnounceValidator` relies on the undocumented
	/// feature that `FuturesUnordered` can be polled and repeatedly yield
	/// `Poll::Ready(None)` after all the futures in it have resolved.
	#[tokio::test]
	async fn deplenished_futures_unordered_can_be_polled() {
		let mut unordered = FuturesUnordered::<BoxFuture<()>>::default();

		unordered.push(futures::future::ready(()).boxed());
		assert_eq!(unordered.next().await, Some(()));

		futures::future::poll_fn(|cx| {
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));
			assert_eq!(unordered.poll_next_unpin(cx), Poll::Ready(None));

			Poll::Ready(())
		})
		.await;
	}

	#[test]
	fn allocate_one_validation_slot() {
		let mut validator =
			BlockAnnounceValidator::<Block>::new(Box::new(DefaultBlockAnnounceValidator {}));
		let peer_id = PeerId::random();

		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::Allocated,
		));
	}

	#[test]
	fn allocate_validation_slots_for_two_peers() {
		let mut validator =
			BlockAnnounceValidator::<Block>::new(Box::new(DefaultBlockAnnounceValidator {}));
		let peer_id_1 = PeerId::random();
		let peer_id_2 = PeerId::random();

		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id_1),
			AllocateSlotForBlockAnnounceValidation::Allocated,
		));
		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id_2),
			AllocateSlotForBlockAnnounceValidation::Allocated,
		));
	}

	#[test]
	fn maximum_validation_slots_per_peer() {
		let mut validator =
			BlockAnnounceValidator::<Block>::new(Box::new(DefaultBlockAnnounceValidator {}));
		let peer_id = PeerId::random();

		for _ in 0..MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS_PER_PEER {
			assert!(matches!(
				validator.allocate_slot_for_block_announce_validation(&peer_id),
				AllocateSlotForBlockAnnounceValidation::Allocated,
			));
		}

		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::MaximumPeerSlotsReached,
		));
	}

	#[test]
	fn validation_slots_per_peer_deallocated() {
		let mut validator =
			BlockAnnounceValidator::<Block>::new(Box::new(DefaultBlockAnnounceValidator {}));
		let peer_id = PeerId::random();

		for _ in 0..MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS_PER_PEER {
			assert!(matches!(
				validator.allocate_slot_for_block_announce_validation(&peer_id),
				AllocateSlotForBlockAnnounceValidation::Allocated,
			));
		}

		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::MaximumPeerSlotsReached,
		));

		validator.deallocate_slot_for_block_announce_validation(&peer_id);

		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::Allocated,
		));
	}

	#[test]
	fn maximum_validation_slots_for_all_peers() {
		let mut validator =
			BlockAnnounceValidator::<Block>::new(Box::new(DefaultBlockAnnounceValidator {}));

		for _ in 0..MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS {
			validator.validations.push(
				futures::future::ready(BlockAnnounceValidationResult::Skip {
					peer_id: PeerId::random(),
				})
				.boxed(),
			)
		}

		let peer_id = PeerId::random();
		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::TotalMaximumSlotsReached,
		));
	}
}
