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
use std::convert::TryInto;
use std::fmt::Debug;
use std::sync::Arc;

use codec::{Codec, Decode, Encode};
use futures::{future, FutureExt, Stream, StreamExt};
use log::{debug, error, info, trace, warn};
use parking_lot::Mutex;

use beefy_primitives::{
	ecdsa::{AuthorityId, AuthoritySignature},
	BeefyApi, BEEFY_ENGINE_ID, KEY_TYPE,
};

use sc_client_api::{Backend as BackendT, BlockchainEvents, FinalityNotification, Finalizer};
use sc_network_gossip::{
	GossipEngine, Network as GossipNetwork, ValidationResult as GossipValidationResult, Validator as GossipValidator,
	ValidatorContext as GossipValidatorContext,
};
use sp_api::{BlockId, ProvideRuntimeApi};
use sp_blockchain::HeaderBackend;
use sp_consensus::SyncOracle as SyncOracleT;
use sp_core::Public;
use sp_keystore::{SyncCryptoStore, SyncCryptoStorePtr};
use sp_runtime::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, NumberFor, Zero};

pub const BEEFY_PROTOCOL_NAME: &str = "/paritytech/beefy/1";

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

fn threshold(voters: usize) -> usize {
	let faulty = voters.saturating_sub(1) / 3;
	voters - faulty
}

struct Rounds<Hash, Id, Signature> {
	rounds: BTreeMap<Hash, RoundTracker<Id, Signature>>,
	voters: Vec<Id>,
}

impl<Hash, Id, Signature> Rounds<Hash, Id, Signature>
where
	Hash: Ord,
{
	fn new(voters: Vec<Id>) -> Self {
		Rounds {
			rounds: BTreeMap::new(),
			voters,
		}
	}
}

impl<Hash, Id, Signature> Rounds<Hash, Id, Signature>
where
	Hash: Ord,
	Id: PartialEq,
	Signature: PartialEq,
{
	fn add_vote(&mut self, round: Hash, vote: (Id, Signature)) -> bool {
		self.rounds.entry(round).or_default().add_vote(vote)
	}

	fn is_done(&self, round: &Hash) -> bool {
		self.rounds
			.get(round)
			.map(|tracker| tracker.is_done(threshold(self.voters.len())))
			.unwrap_or(false)
	}

	fn drop(&mut self, round: &Hash) {
		self.rounds.remove(round);
	}
}

fn topic<Block: BlockT>() -> Block::Hash {
	<<Block::Header as HeaderT>::Hashing as HashT>::hash(b"beefy")
}

#[derive(Debug, Decode, Encode)]
struct VoteMessage<Hash, Id, Signature> {
	block: Hash,
	id: Id,
	signature: Signature,
}

struct BeefyWorker<Block: BlockT, Id, Signature, FinalityNotifications> {
	local_id: Id,
	key_store: SyncCryptoStorePtr,
	min_interval: u32,
	rounds: Rounds<Block::Hash, Id, Signature>,
	finality_notifications: FinalityNotifications,
	gossip_engine: Arc<Mutex<GossipEngine<Block>>>,
	best_finalized_block: NumberFor<Block>,
	best_block_voted_on: NumberFor<Block>,
}

impl<Block, Id, Signature, FinalityNotifications> BeefyWorker<Block, Id, Signature, FinalityNotifications>
where
	Block: BlockT,
{
	fn new(
		local_id: Id,
		key_store: SyncCryptoStorePtr,
		voters: Vec<Id>,
		finality_notifications: FinalityNotifications,
		gossip_engine: GossipEngine<Block>,
		best_finalized_block: NumberFor<Block>,
		best_block_voted_on: NumberFor<Block>,
	) -> Self {
		BeefyWorker {
			local_id,
			key_store,
			min_interval: 2,
			rounds: Rounds::new(voters),
			finality_notifications,
			gossip_engine: Arc::new(Mutex::new(gossip_engine)),
			best_finalized_block,
			best_block_voted_on,
		}
	}
}

impl<Block, Id, Signature, FinalityNotifications> BeefyWorker<Block, Id, Signature, FinalityNotifications>
where
	Block: BlockT,
	Id: Codec + Debug + PartialEq + Public,
	Signature: Codec + Debug + PartialEq + std::convert::TryFrom<Vec<u8>>,
	FinalityNotifications: Stream<Item = FinalityNotification<Block>> + Unpin,
{
	fn should_vote_on(&self, number: NumberFor<Block>) -> bool {
		use sp_runtime::traits::Saturating;
		use sp_runtime::SaturatedConversion;

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
		info!(target: "beefy", "🥩 Finality notification: {:?}", notification);

		if self.should_vote_on(*notification.header.number()) {
			let signature = match SyncCryptoStore::sign_with(
				&*self.key_store,
				KEY_TYPE,
				&self.local_id.to_public_crypto_pair(),
				&notification.header.hash().encode(),
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
				block: notification.header.hash(),
				id: self.local_id.clone(),
				signature,
			};

			self.gossip_engine
				.lock()
				.gossip_message(topic::<Block>(), message.encode(), false);

			debug!(target: "beefy", "Sent vote message: {:?}", message);

			self.handle_vote(message.block, (message.id, message.signature));
		}

		self.best_finalized_block = *notification.header.number();
	}

	fn handle_vote(&mut self, round: Block::Hash, vote: (Id, Signature)) {
		// TODO: validate signature
		let vote_added = self.rounds.add_vote(round, vote);
		if vote_added && self.rounds.is_done(&round) {
			info!(target: "beefy", "🥩 Round {:?} concluded.", round);
			self.rounds.drop(&round);
		}
	}

	async fn run(mut self) {
		let mut votes = Box::pin(self.gossip_engine.lock().messages_for(topic::<Block>()).filter_map(
			|notification| async move {
				debug!(target: "beefy", "Got vote message: {:?}", notification);

				VoteMessage::<Block::Hash, Id, Signature>::decode(&mut &notification.message[..]).ok()
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
						self.handle_vote(vote.block, (vote.id, vote.signature));
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

pub async fn start_beefy_gadget<Block, Backend, Client, Network, SyncOracle>(
	client: Arc<Client>,
	key_store: SyncCryptoStorePtr,
	network: Network,
	_sync_oracle: SyncOracle,
) where
	Block: BlockT,
	Backend: BackendT<Block>,
	Client: BlockchainEvents<Block>
		+ HeaderBackend<Block>
		+ Finalizer<Block, Backend>
		+ ProvideRuntimeApi<Block>
		+ Send
		+ Sync,
	Client::Api: BeefyApi<Block, AuthorityId>,
	Network: GossipNetwork<Block> + Clone + Send + 'static,
	SyncOracle: SyncOracleT + Send + 'static,
{
	let gossip_engine = GossipEngine::new(
		network,
		BEEFY_ENGINE_ID,
		BEEFY_PROTOCOL_NAME,
		Arc::new(AllowAll {
			topic: topic::<Block>(),
		}),
	);

	let at = BlockId::hash(client.info().best_hash);
	let voters = client
		.runtime_api()
		.authorities(&at)
		.expect("Failed to get BEEFY authorities");

	let local_id = match voters
		.iter()
		.find(|id| SyncCryptoStore::has_keys(&*key_store, &[(id.to_raw_vec(), KEY_TYPE)]))
	{
		Some(id) => {
			info!(target: "beefy", "🥩 Starting BEEFY worker with local id: {:?}", id);
			id.clone()
		}
		None => {
			info!(target: "beefy", "🥩 No local id found, not starting BEEFY worker.");
			return futures::future::pending().await;
		}
	};

	let best_finalized_block = client.info().finalized_number;
	let best_block_voted_on = Zero::zero();

	let worker = BeefyWorker::<_, AuthorityId, AuthoritySignature, _>::new(
		local_id,
		key_store,
		voters,
		client.finality_notification_stream(),
		gossip_engine,
		best_finalized_block,
		best_block_voted_on,
	);

	worker.run().await
}

#[cfg(test)]
mod tests {
	#[test]
	fn it_works() {
		assert_eq!(2 + 2, 4);
	}
}
