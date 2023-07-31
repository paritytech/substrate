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

/// Maximum number of concurrent block announce validations.
///
/// If the queue reaches the maximum, we drop any new block
/// announcements.
const MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS: usize = 256;

/// Maximum number of concurrent block announce validations per peer.
///
/// See [`MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS`] for more information.
const MAX_CONCURRENT_BLOCK_ANNOUNCE_VALIDATIONS_PER_PEER: usize = 4;

/// Result of [`BlockAnnounceValidator::block_announce_validation`].
#[derive(Debug, Clone, PartialEq, Eq)]
enum PreValidateBlockAnnounce<H> {
	/// The announcement failed at validation.
	///
	/// The peer reputation should be decreased.
	Failure {
		/// The id of the peer that send us the announcement.
		peer_id: PeerId,
		/// Should the peer be disconnected?
		disconnect: bool,
	},
	/// The pre-validation was sucessful and the announcement should be
	/// further processed.
	Process {
		/// Is this the new best block of the peer?
		is_new_best: bool,
		/// The id of the peer that send us the announcement.
		peer_id: PeerId,
		/// The announcement.
		announce: BlockAnnounce<H>,
	},
	/// The announcement validation returned an error.
	///
	/// An error means that *this* node failed to validate it because some internal error happened.
	/// If the block announcement was invalid, [`Self::Failure`] is the correct variant to express
	/// this.
	Error { peer_id: PeerId },
}

impl<H> PreValidateBlockAnnounce<H> {
	fn peer_id(&self) -> &PeerId {
		match self {
			PreValidateBlockAnnounce::Failure { peer_id, .. } |
			PreValidateBlockAnnounce::Process { peer_id, .. } |
			PreValidateBlockAnnounce::Error { peer_id } => peer_id,
		}
	}
}

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
	Skip,
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
	validations:
		FuturesUnordered<Pin<Box<dyn Future<Output = PreValidateBlockAnnounce<B::Header>> + Send>>>,
	/// Number of concurrent block announce validations per peer.
	validations_per_peer: HashMap<PeerId, usize>,
}

impl<B: BlockT> BlockAnnounceValidator<B> {
	pub(crate) fn new(
		validator: Box<dyn sp_consensus::block_validation::BlockAnnounceValidator<B> + Send>,
	) -> Self {
		Self {
			validator,
			validations: Default::default(),
			validations_per_peer: Default::default(),
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
			target: "sync",
			"Pre-validating received block announcement {:?} with number {:?} from {}",
			hash,
			number,
			peer_id,
		);

		if number.is_zero() {
			warn!(
				target: "sync",
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
					target: "sync",
					"💔 Ignored block (#{} -- {}) announcement from {} because all validation slots are occupied.",
					number,
					hash,
					peer_id,
				);
				return
			},
			AllocateSlotForBlockAnnounceValidation::MaximumPeerSlotsReached => {
				warn!(
					target: "sync",
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
					Ok(Validation::Success { is_new_best }) => PreValidateBlockAnnounce::Process {
						is_new_best: is_new_best || is_best,
						announce,
						peer_id,
					},
					Ok(Validation::Failure { disconnect }) => {
						debug!(
							target: "sync",
							"Block announcement validation of block {:?} from {} failed",
							hash,
							peer_id,
						);
						PreValidateBlockAnnounce::Failure { peer_id, disconnect }
					},
					Err(e) => {
						debug!(
							target: "sync",
							"💔 Block announcement validation of block {:?} errored: {}",
							hash,
							e,
						);
						PreValidateBlockAnnounce::Error { peer_id }
					},
				}
			}
			.boxed(),
		);
	}

	// TODO: merge this code into future above.
	fn handle_pre_validation(
		pre_validation: PreValidateBlockAnnounce<B::Header>,
	) -> BlockAnnounceValidationResult<B::Header> {
		match pre_validation {
			PreValidateBlockAnnounce::Process { is_new_best, peer_id, announce } => {
				trace!(
					target: "sync",
					"Finished block announce validation: from {:?}: {:?}. local_best={}",
					peer_id,
					announce.summary(),
					is_new_best,
				);

				BlockAnnounceValidationResult::Process { is_new_best, peer_id, announce }
			},
			PreValidateBlockAnnounce::Failure { peer_id, disconnect } => {
				debug!(
					target: "sync",
					"Failed announce validation: {:?}, disconnect: {}",
					peer_id,
					disconnect,
				);
				BlockAnnounceValidationResult::Failure { peer_id, disconnect }
			},
			PreValidateBlockAnnounce::Error { peer_id } => {
				debug!(
					target: "sync",
					"Ignored announce validation from {:?} due to internal validation error",
					peer_id,
				);
				BlockAnnounceValidationResult::Skip
			},
		}
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
					target: "sync",
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
						target: "sync",
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
		match self.validations.poll_next_unpin(cx) {
			Poll::Ready(Some(pre_validation)) => {
				self.deallocate_slot_for_block_announce_validation(pre_validation.peer_id());

				let validation = Self::handle_pre_validation(pre_validation);

				Poll::Ready(Some(validation))
			},
			_ => Poll::Pending,
		}
	}
}
