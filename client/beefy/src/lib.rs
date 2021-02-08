// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

use std::collections::BTreeMap;
use std::convert::{TryFrom, TryInto};
use std::fmt::Debug;
use std::sync::Arc;

use codec::{Codec, Decode, Encode};
use futures::{future, FutureExt, Stream, StreamExt};
use log::{debug, error, info, trace, warn};
use parking_lot::Mutex;

use beefy_primitives::{BeefyApi, Commitment, ConsensusLog, MmrRootHash, SignedCommitment, BEEFY_ENGINE_ID, KEY_TYPE};

use sc_client_api::{Backend as BackendT, BlockchainEvents, FinalityNotification, Finalizer};
use sc_network_gossip::{
	GossipEngine, Network as GossipNetwork, ValidationResult as GossipValidationResult, Validator as GossipValidator,
	ValidatorContext as GossipValidatorContext,
};
use sp_api::{BlockId, ProvideRuntimeApi};
use sp_application_crypto::{AppPublic, Public};
use sp_blockchain::HeaderBackend;
use sp_consensus::SyncOracle as SyncOracleT;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::{
	generic::OpaqueDigestItemId,
	traits::{Block as BlockT, Hash as HashT, Header as HeaderT, NumberFor, Zero},
};

pub mod notification;

use notification::BeefySignedCommitmentSender;

pub const BEEFY_PROTOCOL_NAME: &str = "/paritytech/beefy/1";

/// Returns the configuration value to put in
/// [`sc_network::config::NetworkConfiguration::extra_sets`].
pub fn beefy_peers_set_config() -> sc_network::config::NonDefaultSetConfig {
	sc_network::config::NonDefaultSetConfig {
		notifications_protocol: BEEFY_PROTOCOL_NAME.into(),
		max_notification_size: 1024 * 1024,
		set_config: sc_network::config::SetConfig {
			in_peers: 25,
			out_peers: 25,
			reserved_nodes: Vec::new(),
			non_reserved_mode: sc_network::config::NonReservedPeerMode::Accept,
		},
	}
}

/// Allows all gossip messages to get through.
struct AllowAll<Hash> {
	topic: Hash,
}

impl<Block> GossipValidator<Block> for AllowAll<Block::Hash>
where
	Block: BlockT,
{
	fn validate(
		&self,
		_context: &mut dyn GossipValidatorContext<Block>,
		_sender: &sc_network::PeerId,
		_data: &[u8],
	) -> GossipValidationResult<Block::Hash> {
		GossipValidationResult::ProcessAndKeep(self.topic)
	}
}

struct RoundTracker<Id, Signature> {
	votes: Vec<(Id, Signature)>,
}

impl<Id, Signature> Default for RoundTracker<Id, Signature> {
	fn default() -> Self {
		RoundTracker { votes: Vec::new() }
	}
}

impl<Id, Signature> RoundTracker<Id, Signature>
where
	Id: PartialEq,
	Signature: PartialEq,
{
	fn add_vote(&mut self, vote: (Id, Signature)) -> bool {
		// this needs to handle equivocations in the future
		if self.votes.contains(&vote) {
			return false;
		}

		self.votes.push(vote);
		true
	}

	fn is_done(&self, threshold: usize) -> bool {
		self.votes.len() >= threshold
	}
}

fn threshold(authorities: usize) -> usize {
	let faulty = authorities.saturating_sub(1) / 3;
	authorities - faulty
}

struct Rounds<Hash, Number, Id, Signature> {
	rounds: BTreeMap<(Hash, Number), RoundTracker<Id, Signature>>,
	authorities: Vec<Id>,
}

impl<Hash, Number, Id, Signature> Rounds<Hash, Number, Id, Signature>
where
	Hash: Ord,
	Number: Ord,
{
	fn new(authorities: Vec<Id>) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			authorities,
		}
	}
}

impl<Hash, Number, Id, Signature> Rounds<Hash, Number, Id, Signature>
where
	Hash: Ord,
	Number: Ord,
	Id: PartialEq,
	Signature: Clone + PartialEq,
{
	fn add_vote(&mut self, round: (Hash, Number), vote: (Id, Signature)) -> bool {
		self.rounds.entry(round).or_default().add_vote(vote)
	}

	fn is_done(&self, round: &(Hash, Number)) -> bool {
		self.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.authorities.len())))
			.unwrap_or(false)
	}

	fn drop(&mut self, round: &(Hash, Number)) -> Option<Vec<Option<Signature>>> {
		let signatures = self.rounds.remove(round)?.votes;

		Some(
			self.authorities
				.iter()
				.map(|authority_id| {
					signatures
						.iter()
						.find_map(|(id, sig)| if id == authority_id { Some(sig.clone()) } else { None })
				})
				.collect(),
		)
	}
}

fn topic<Block: BlockT>() -> Block::Hash {
	<<Block::Header as HeaderT>::Hashing as HashT>::hash(b"beefy")
}

#[derive(Debug, Decode, Encode)]
struct VoteMessage<Hash, Number, Id, Signature> {
	commitment: Commitment<Number, Hash>,
	id: Id,
	signature: Signature,
}

enum BeefyId<Id> {
	Validator(Id),
	None,
}

struct BeefyWorker<Block: BlockT, Id, Signature, FinalityNotifications> {
	local_id: BeefyId<Id>,
	key_store: SyncCryptoStorePtr,
	min_interval: u32,
	rounds: Rounds<MmrRootHash, NumberFor<Block>, Id, Signature>,
	finality_notifications: FinalityNotifications,
	gossip_engine: Arc<Mutex<GossipEngine<Block>>>,
	signed_commitment_sender: BeefySignedCommitmentSender<Block, Signature>,
	best_finalized_block: NumberFor<Block>,
	best_block_voted_on: NumberFor<Block>,
}

impl<Block, Id, Signature, FinalityNotifications> BeefyWorker<Block, Id, Signature, FinalityNotifications>
where
	Block: BlockT,
{
	#[allow(clippy::too_many_arguments)]
	fn new(
		local_id: BeefyId<Id>,
		key_store: SyncCryptoStorePtr,
		authorities: Vec<Id>,
		finality_notifications: FinalityNotifications,
		gossip_engine: GossipEngine<Block>,
		signed_commitment_sender: BeefySignedCommitmentSender<Block, Signature>,
		best_finalized_block: NumberFor<Block>,
		best_block_voted_on: NumberFor<Block>,
	) -> Self {
		BeefyWorker {
			local_id,
			key_store,
			min_interval: 2,
			rounds: Rounds::new(authorities),
			finality_notifications,
			gossip_engine: Arc::new(Mutex::new(gossip_engine)),
			signed_commitment_sender,
			best_finalized_block,
			best_block_voted_on,
		}
	}
}

impl<Block, Id, Signature, FinalityNotifications> BeefyWorker<Block, Id, Signature, FinalityNotifications>
where
	Block: BlockT,
	Id: Codec + Debug + PartialEq + Public,
	Signature: Clone + Codec + Debug + PartialEq + std::convert::TryFrom<Vec<u8>>,
	FinalityNotifications: Stream<Item = FinalityNotification<Block>> + Unpin,
{
	fn should_vote_on(&self, number: NumberFor<Block>) -> bool {
		use sp_runtime::traits::Saturating;
		use sp_runtime::SaturatedConversion;

		// we only vote as a validator
		if let BeefyId::None = self.local_id {
			return false;
		}

		let diff = self.best_finalized_block.saturating_sub(self.best_block_voted_on);
		let diff = diff.saturated_into::<u32>();
		let next_power_of_two = (diff / 2).next_power_of_two();
		let next_block_to_vote_on = self.best_block_voted_on + self.min_interval.max(next_power_of_two).into();

		trace!(
			target: "beefy",
			"should_vote_on: #{:?}, diff: {:?}, next_power_of_two: {:?}, next_block_to_vote_on: #{:?}",
			number,
			diff,
			next_power_of_two,
			next_block_to_vote_on,
		);

		number == next_block_to_vote_on
	}

	fn handle_finality_notification(&mut self, notification: FinalityNotification<Block>) {
		debug!(target: "beefy", "Finality notification: {:?}", notification);

		if self.should_vote_on(*notification.header.number()) {
			let local_id = if let BeefyId::Validator(id) = &self.local_id {
				id
			} else {
				warn!(target: "beefy", "🥩 Missing validator id - can't vote for: {:?}", notification.header.hash());
				return;
			};

			let mmr_root = if let Some(hash) = find_mmr_root_digest::<Block, Id>(&notification.header) {
				hash
			} else {
				warn!(target: "beefy", "🥩 No MMR root digest found for: {:?}", notification.header.hash());
				return;
			};

			// TODO: this needs added support for validator set changes (and abstracting the
			// "thing to sign" would be nice).
			let commitment = Commitment {
				payload: mmr_root,
				block_number: notification.header.number(),
				validator_set_id: 0,
			};

			let signature = match SyncCryptoStore::sign_with(
				&*self.key_store,
				KEY_TYPE,
				&local_id.to_public_crypto_pair(),
				&commitment.encode(),
			)
			.map_err(|_| ())
			.and_then(|res| res.try_into().map_err(|_| ()))
			{
				Ok(sig) => sig,
				Err(err) => {
					warn!(target: "beefy", "Error signing: {:?}", err);
					return;
				}
			};

			self.best_block_voted_on = *notification.header.number();

			let message = VoteMessage {
				commitment,
				id: local_id.clone(),
				signature,
			};

			self.gossip_engine
				.lock()
				.gossip_message(topic::<Block>(), message.encode(), false);

			debug!(target: "beefy", "Sent vote message: {:?}", message);

			self.handle_vote(
				(message.commitment.payload, *message.commitment.block_number),
				(message.id, message.signature),
			);
		}

		self.best_finalized_block = *notification.header.number();
	}

	fn handle_vote(&mut self, round: (MmrRootHash, NumberFor<Block>), vote: (Id, Signature)) {
		// TODO: validate signature
		let vote_added = self.rounds.add_vote(round, vote);

		if vote_added && self.rounds.is_done(&round) {
			if let Some(signatures) = self.rounds.drop(&round) {
				// TODO: this needs added support for validator set changes (and abstracting the
				// "thing to sign" would be nice).
				let commitment = Commitment {
					payload: round.0,
					block_number: round.1,
					validator_set_id: 0,
				};

				let signed_commitment = SignedCommitment { commitment, signatures };

				info!(target: "beefy", "🥩 Round #{} concluded, committed: {:?}.", round.1, signed_commitment);

				self.signed_commitment_sender.notify(signed_commitment);
			}
		}
	}

	async fn run(mut self) {
		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<Block>()).filter_map(
			|notification| async move {
				debug!(target: "beefy", "Got vote message: {:?}", notification);

				VoteMessage::<MmrRootHash, NumberFor<Block>, Id, Signature>::decode(&mut &notification.message[..]).ok()
			},
		));

		loop {
			let engine = self.gossip_engine.clone();
			let gossip_engine = future::poll_fn(|cx| engine.lock().poll_unpin(cx));

			futures::select! {
				notification = self.finality_notifications.next().fuse() => {
					if let Some(notification) = notification {
						self.handle_finality_notification(notification);
					} else {
						return;
					}
				},
				vote = votes.next() => {
					if let Some(vote) = vote {
						self.handle_vote(
							(vote.commitment.payload, vote.commitment.block_number),
							(vote.id, vote.signature),
						);
					} else {
						return;
					}
				},
				_ = gossip_engine.fuse() => {
					error!(target: "beefy", "Gossip engine has terminated.");
					return;
				}
			}
		}
	}
}

pub async fn start_beefy_gadget<Block, Pair, Backend, Client, Network, SyncOracle>(
	client: Arc<Client>,
	key_store: SyncCryptoStorePtr,
	network: Network,
	signed_commitment_sender: BeefySignedCommitmentSender<Block, Pair::Signature>,
	_sync_oracle: SyncOracle,
) where
	Block: BlockT,
	Pair: sp_core::Pair,
	Pair::Public: AppPublic + Codec,
	Pair::Signature: Clone + Codec + Debug + PartialEq + TryFrom<Vec<u8>>,
	Backend: BackendT<Block>,
	Client: BlockchainEvents<Block>
		+ HeaderBackend<Block>
		+ Finalizer<Block, Backend>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: BeefyApi<Block, Pair::Public>,
	Network: GossipNetwork<Block> + Clone + Send + 'static,
	SyncOracle: SyncOracleT + Send + 'static,
{
	let gossip_engine = GossipEngine::new(
		network,
		BEEFY_PROTOCOL_NAME,
		Arc::new(AllowAll {
			topic: topic::<Block>(),
		}),
		None,
	);

	let at = BlockId::hash(client.info().best_hash);
	let authorities = client
		.runtime_api()
		.authorities(&at)
		.expect("Failed to get BEEFY authorities");

	let local_id = match authorities
		.iter()
		.find(|id| SyncCryptoStore::has_keys(&*key_store, &[(id.to_raw_vec(), KEY_TYPE)]))
	{
		Some(id) => {
			info!(target: "beefy", "🥩 Starting BEEFY worker with local id: {:?}", id);
			BeefyId::Validator(id.clone())
		}
		None => {
			info!(target: "beefy", "🥩 No local id found, BEEFY worker will be gossip only.");
			BeefyId::None
		}
	};

	let best_finalized_block = client.info().finalized_number;
	let best_block_voted_on = Zero::zero();

	let worker = BeefyWorker::<_, Pair::Public, Pair::Signature, _>::new(
		local_id,
		key_store,
		authorities,
		client.finality_notification_stream(),
		gossip_engine,
		signed_commitment_sender,
		best_finalized_block,
		best_block_voted_on,
	);

	worker.run().await
}

/// Extract the MMR root hash from a digest in the given header, if it exists.
fn find_mmr_root_digest<Block: BlockT, Id>(header: &Block::Header) -> Option<MmrRootHash>
where
	Id: Codec,
{
	header.digest().logs().iter().find_map(|log| {
		match log.try_to::<ConsensusLog<Id>>(OpaqueDigestItemId::Consensus(&BEEFY_ENGINE_ID)) {
			Some(ConsensusLog::MmrRoot(root)) => Some(root),
			_ => None,
		}
	})
}
