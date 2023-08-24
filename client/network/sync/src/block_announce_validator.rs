// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::futures_stream::{futures_stream, FuturesStreamReceiver, FuturesStreamSender};
use futures::{Future, FutureExt, Stream, StreamExt};
use libp2p::PeerId;
use log::{debug, error, trace, warn};
use sc_network_common::sync::message::BlockAnnounce;
use sp_consensus::block_validation::Validation;
use sp_runtime::traits::{Block as BlockT, Header, Zero};
use std::{
	collections::{hash_map::Entry, HashMap},
	default::Default,
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
	/// All block announcements that are currently being validated, sending side of the stream.
	tx_validations: FuturesStreamSender<
		Pin<Box<dyn Future<Output = BlockAnnounceValidationResult<B::Header>> + Send>>,
	>,
	/// All block announcements that are currently being validated, receiving side of the stream.
	rx_validations: FuturesStreamReceiver<
		Pin<Box<dyn Future<Output = BlockAnnounceValidationResult<B::Header>> + Send>>,
	>,
	/// Number of concurrent block announce validations per peer.
	validations_per_peer: HashMap<PeerId, usize>,
}

impl<B: BlockT> BlockAnnounceValidator<B> {
	pub(crate) fn new(
		validator: Box<dyn sp_consensus::block_validation::BlockAnnounceValidator<B> + Send>,
	) -> Self {
		let (tx_validations, rx_validations) = futures_stream(
			"mpsc_block_announce_validation_stream",
			MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS + 1,
		);
		Self { validator, tx_validations, rx_validations, validations_per_peer: Default::default() }
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

		let _ = self.tx_validations.push(
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
		if self.rx_validations.len_lower_bound() >= MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS {
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
					"💔 Block announcement validation from peer {} finished for a slot that was not allocated!",
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
		if let Some(validation) = futures::ready!(self.rx_validations.poll_next_unpin(cx)) {
			self.deallocate_slot_for_block_announce_validation(validation.peer_id());

			Poll::Ready(Some(validation))
		} else {
			trace!(
				target: LOG_TARGET,
				"Block announce validations stream terminated, terminating `BlockAnnounceValidator`",
			);
			Poll::Ready(None)
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;
	use crate::block_announce_validator::AllocateSlotForBlockAnnounceValidation;
	use libp2p::PeerId;
	use sp_consensus::block_validation::DefaultBlockAnnounceValidator;
	use substrate_test_runtime_client::runtime::Block;

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
			let _ = validator.tx_validations.push(
				futures::future::ready(BlockAnnounceValidationResult::Skip {
					peer_id: PeerId::random(),
				})
				.boxed(),
			);
		}

		let peer_id = PeerId::random();
		assert!(matches!(
			validator.allocate_slot_for_block_announce_validation(&peer_id),
			AllocateSlotForBlockAnnounceValidation::TotalMaximumSlotsReached,
		));
	}
}
