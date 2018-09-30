// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! This service uses BFT consensus provided by the substrate.

extern crate parking_lot;
extern crate node_transaction_pool as transaction_pool;
extern crate node_runtime;
extern crate node_primitives;

extern crate substrate_bft as bft;
extern crate parity_codec as codec;
extern crate substrate_primitives as primitives;
extern crate sr_primitives as runtime_primitives;
extern crate srml_system;
extern crate substrate_client as client;

extern crate exit_future;
extern crate tokio;
extern crate rhododendron;

#[macro_use]
extern crate error_chain;
extern crate futures;

#[macro_use]
extern crate log;

#[cfg(test)]
extern crate substrate_keyring;

use std::sync::Arc;
use std::time::{self, Duration, Instant};

use client::{Client as SubstrateClient, CallExecutor};
use codec::{Decode, Encode};
use node_primitives::{AccountId, Timestamp, SessionKey, InherentData};
use node_runtime::Runtime;
use primitives::{AuthorityId, ed25519, Blake2Hasher};
use runtime_primitives::traits::{Block as BlockT, Hash as HashT, Header as HeaderT, As};
use runtime_primitives::generic::{BlockId, Era};
use srml_system::Trait as SystemT;
use transaction_pool::{TransactionPool, Client as TPClient};
use tokio::runtime::TaskExecutor;
use tokio::timer::Delay;

use futures::prelude::*;
use futures::future;
use parking_lot::RwLock;

pub use self::error::{ErrorKind, Error, Result};
pub use self::offline_tracker::OfflineTracker;
pub use service::Service;

mod evaluation;
mod error;
mod offline_tracker;
mod service;

/// Shared offline validator tracker.
pub type SharedOfflineTracker = Arc<RwLock<OfflineTracker>>;

// block size limit.
const MAX_TRANSACTIONS_SIZE: usize = 4 * 1024 * 1024;

/// Build new blocks.
pub trait BlockBuilder<Block: BlockT> {
	/// Push an extrinsic onto the block. Fails if the extrinsic is invalid.
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<()>;

	/// Bake the block with provided extrinsics.
	fn bake(self) -> Result<Block>;
}

/// Local client abstraction for the consensus.
pub trait AuthoringApi: Send + Sync {
	/// The block used for this API type.
	type Block: BlockT;
	/// The block builder for this API type.
	type BlockBuilder: BlockBuilder<Self::Block>;

	/// Get the value of the randomness beacon at a given block.
	fn random_seed(&self, at: &BlockId<Self::Block>) -> Result<<Self::Block as BlockT>::Hash>;

	/// Get validators at a given block.
	fn validators(&self, at: &BlockId<Self::Block>) -> Result<Vec<AccountId>>;

	/// Build a block on top of the given, with inherent extrinsics pre-pushed.
	fn build_block(&self, at: &BlockId<Self::Block>, inherent_data: InherentData) -> Result<Self::BlockBuilder>;

	/// Get the nonce (né index) of an account at a block.
	fn index(&self, at: &BlockId<Self::Block>, account: AccountId) -> Result<u64>;

	/// Attempt to produce the (encoded) inherent extrinsics for a block being built upon the given.
	/// This may vary by runtime and will fail if a runtime doesn't follow the same API.
	fn inherent_extrinsics(&self, at: &BlockId<Self::Block>, inherent_data: InherentData) -> Result<Vec<<Self::Block as BlockT>::Extrinsic>>;

	/// Evaluate a block. Returns true if the block is good, false if it is known to be bad,
	/// and an error if we can't evaluate for some reason.
	fn evaluate_block(&self, at: &BlockId<Self::Block>, block: Self::Block) -> Result<bool>;
}

impl<B, E, Block> BlockBuilder<Block> for client::block_builder::BlockBuilder<B, E, Block, Blake2Hasher> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT
{
	fn push_extrinsic(&mut self, extrinsic: <Block as BlockT>::Extrinsic) -> Result<()> {
		client::block_builder::BlockBuilder::push(self, extrinsic).map_err(Into::into)
	}

	fn bake(self) -> Result<Block> {
		client::block_builder::BlockBuilder::bake(self).map_err(Into::into)
	}
}

impl<B, E, Block> AuthoringApi for SubstrateClient<B, E, Block> where
	B: client::backend::Backend<Block, Blake2Hasher> + Send + Sync + 'static,
	E: CallExecutor<Block, Blake2Hasher> + Send + Sync + Clone + 'static,
	Block: BlockT,
{
	type Block = Block;
	type BlockBuilder = client::block_builder::BlockBuilder<B, E, Block, Blake2Hasher>;

	fn random_seed(&self, at: &BlockId<Block>) -> Result<<Self::Block as BlockT>::Hash> {
		self.call_api_at(at, "random_seed", &()).map_err(Into::into)
	}

	fn validators(&self, at: &BlockId<Block>) -> Result<Vec<AccountId>> {
		self.call_api_at(at, "validators", &()).map_err(Into::into)
	}

	fn build_block(&self, at: &BlockId<Block>, inherent_data: InherentData) -> Result<Self::BlockBuilder> {
		let runtime_version = self.runtime_version_at(at)?;

		let mut block_builder = self.new_block_at(at)?;
		if runtime_version.has_api(*b"inherent", 1) {
			for inherent in self.inherent_extrinsics(at, inherent_data)? {
				block_builder.push(inherent)?;
			}
		}
		Ok(block_builder)
	}

	fn index(&self, at: &BlockId<Block>, account: AccountId) -> Result<u64> {
		self.call_api_at(at, "account_nonce", &account).map_err(Into::into)
	}

	fn inherent_extrinsics(&self, at: &BlockId<Self::Block>, inherent_data: InherentData) -> Result<Vec<<Block as BlockT>::Extrinsic>> {
		self.call_api_at(at, "inherent_extrinsics", &inherent_data).map_err(Into::into)
	}

	fn evaluate_block(&self, at: &BlockId<Self::Block>, block: Self::Block) -> Result<bool> {
		let res: client::error::Result<()> = self.call_api_at(at, "execute_block", &block);
		match res {
			Ok(()) => Ok(true),
			Err(err) => match err.kind() {
				&client::error::ErrorKind::Execution(_) => Ok(false),
				_ => Err(err.into())
			}
		}
	}
}

/// A long-lived network which can create BFT message routing processes on demand.
pub trait Network {
	/// The block used for this API type.
	type Block: BlockT;
	/// The input stream of BFT messages. Should never logically conclude.
	type Input: Stream<Item=bft::Communication<Self::Block>,Error=Error>;
	/// The output sink of BFT messages. Messages sent here should eventually pass to all
	/// current authorities.
	type Output: Sink<SinkItem=bft::Communication<Self::Block>,SinkError=Error>;

	/// Instantiate input and output streams.
	fn communication_for(
		&self,
		validators: &[SessionKey],
		local_id: SessionKey,
		parent_hash: <Self::Block as BlockT>::Hash,
		task_executor: TaskExecutor
	) -> (Self::Input, Self::Output);
}

/// Proposer factory.
pub struct ProposerFactory<N, C> where
	C: AuthoringApi + TPClient,
{
	/// The client instance.
	pub client: Arc<C>,
	/// The transaction pool.
	pub transaction_pool: Arc<TransactionPool<C>>,
	/// The backing network handle.
	pub network: N,
	/// handle to remote task executor
	pub handle: TaskExecutor,
	/// Offline-tracker.
	pub offline: SharedOfflineTracker,
	/// Force delay in evaluation this long.
	pub force_delay: Timestamp,
}

impl<N, C> bft::Environment<<C as AuthoringApi>::Block> for ProposerFactory<N, C> where
	N: Network<Block=<C as AuthoringApi>::Block>,
	C: AuthoringApi + TPClient<Block=<C as AuthoringApi>::Block>,
	<<C as AuthoringApi>::Block as BlockT>::Hash:
		Into<<Runtime as SystemT>::Hash> + PartialEq<primitives::H256> + Into<primitives::H256>
{
	type Proposer = Proposer<C>;
	type Input = N::Input;
	type Output = N::Output;
	type Error = Error;

	fn init(
		&self,
		parent_header: &<<C as AuthoringApi>::Block as BlockT>::Header,
		authorities: &[AuthorityId],
		sign_with: Arc<ed25519::Pair>,
	) -> Result<(Self::Proposer, Self::Input, Self::Output)> {
		use runtime_primitives::traits::Hash as HashT;
		let parent_hash = parent_header.hash();

		let id = BlockId::hash(parent_hash);
		let random_seed = self.client.random_seed(&id)?;
		let random_seed = <<<C as AuthoringApi>::Block as BlockT>::Header as HeaderT>::Hashing::hash(random_seed.as_ref());

		let validators = self.client.validators(&id)?;
		self.offline.write().note_new_block(&validators[..]);

		info!("Starting consensus session on top of parent {:?}", parent_hash);

		let local_id = sign_with.public().0.into();
		let (input, output) = self.network.communication_for(
			authorities,
			local_id,
			parent_hash.clone(),
			self.handle.clone(),
		);
		let now = Instant::now();
		let proposer = Proposer {
			client: self.client.clone(),
			start: now,
			local_key: sign_with,
			parent_hash,
			parent_id: id,
			parent_number: *parent_header.number(),
			random_seed,
			transaction_pool: self.transaction_pool.clone(),
			offline: self.offline.clone(),
			validators,
			minimum_timestamp: current_timestamp() + self.force_delay,
		};

		Ok((proposer, input, output))
	}
}

/// The proposer logic.
pub struct Proposer<C: AuthoringApi + TPClient> {
	client: Arc<C>,
	start: Instant,
	local_key: Arc<ed25519::Pair>,
	parent_hash: <<C as AuthoringApi>::Block as BlockT>::Hash,
	parent_id: BlockId<<C as AuthoringApi>::Block>,
	parent_number: <<<C as AuthoringApi>::Block as BlockT>::Header as HeaderT>::Number,
	random_seed: <<C as AuthoringApi>::Block as BlockT>::Hash,
	transaction_pool: Arc<TransactionPool<C>>,
	offline: SharedOfflineTracker,
	validators: Vec<AccountId>,
	minimum_timestamp: u64,
}

impl<C: AuthoringApi + TPClient> Proposer<C> {
	fn primary_index(&self, round_number: usize, len: usize) -> usize {
		use primitives::uint::U256;

		let big_len = U256::from(len);
		let offset = U256::from_big_endian(self.random_seed.as_ref()) % big_len;
		let offset = offset.low_u64() as usize + round_number;
		offset % len
	}
}

impl<C> bft::Proposer<<C as AuthoringApi>::Block> for Proposer<C> where
	C: AuthoringApi + TPClient<Block=<C as AuthoringApi>::Block>,
	<<C as AuthoringApi>::Block as BlockT>::Hash:
		Into<<Runtime as SystemT>::Hash> + PartialEq<primitives::H256> + Into<primitives::H256>
{
	type Create = Result<<C as AuthoringApi>::Block>;
	type Error = Error;
	type Evaluate = Box<Future<Item=bool, Error=Error>>;

	fn propose(&self) -> Result<<C as AuthoringApi>::Block> {
		use runtime_primitives::traits::BlakeTwo256;

		const MAX_VOTE_OFFLINE_SECONDS: Duration = Duration::from_secs(60);

		// TODO: handle case when current timestamp behind that in state.
		let timestamp = ::std::cmp::max(self.minimum_timestamp, current_timestamp());

		let elapsed_since_start = self.start.elapsed();
		let offline_indices = if elapsed_since_start > MAX_VOTE_OFFLINE_SECONDS {
			Vec::new()
		} else {
			self.offline.read().reports(&self.validators[..])
		};

		if !offline_indices.is_empty() {
			info!(
				"Submitting offline validators {:?} for slash-vote",
				offline_indices.iter().map(|&i| self.validators[i as usize]).collect::<Vec<_>>(),
				)
		}

		let inherent_data = InherentData {
			timestamp,
			offline_indices,
		};

		let mut block_builder = self.client.build_block(&self.parent_id, inherent_data)?;

		{
			let mut unqueue_invalid = Vec::new();
			let result = self.transaction_pool.cull_and_get_pending(&BlockId::hash(self.parent_hash), |pending_iterator| {
				let mut pending_size = 0;
				for pending in pending_iterator {
					if pending_size + pending.verified.encoded_size() >= MAX_TRANSACTIONS_SIZE { break }

					match block_builder.push_extrinsic(pending.original.clone()) {
						Ok(()) => {
							pending_size += pending.verified.encoded_size();
						}
						Err(e) => {
							trace!(target: "transaction-pool", "Invalid transaction: {}", e);
							unqueue_invalid.push(pending.verified.hash().clone());
						}
					}
				}
			});
			if let Err(e) = result {
				warn!("Unable to get the pending set: {:?}", e);
			}

			self.transaction_pool.remove(&unqueue_invalid, false);
		}

		let block = block_builder.bake()?;

		info!("Proposing block [number: {}; hash: {}; parent_hash: {}; extrinsics: [{}]]",
			  block.header().number(),
			  <<C as AuthoringApi>::Block as BlockT>::Hash::from(block.header().hash()),
			  block.header().parent_hash(),
			  block.extrinsics().iter()
			  .map(|xt| format!("{}", BlakeTwo256::hash_of(xt)))
			  .collect::<Vec<_>>()
			  .join(", ")
			 );

		let substrate_block = Decode::decode(&mut block.encode().as_slice())
			.expect("blocks are defined to serialize to substrate blocks correctly; qed");

		assert!(evaluation::evaluate_initial(
			&substrate_block,
			timestamp,
			&self.parent_hash,
			self.parent_number,
		).is_ok());

		Ok(substrate_block)
	}

	fn evaluate(&self, unchecked_proposal: &<C as AuthoringApi>::Block) -> Self::Evaluate {
		debug!(target: "bft", "evaluating block on top of parent ({}, {:?})", self.parent_number, self.parent_hash);

		let current_timestamp = current_timestamp();

		// do initial serialization and structural integrity checks.
		let maybe_proposal = evaluation::evaluate_initial(
			unchecked_proposal,
			current_timestamp,
			&self.parent_hash,
			self.parent_number,
		);

		let proposal = match maybe_proposal {
			Ok(p) => p,
			Err(e) => {
				// TODO: these errors are easily re-checked in runtime.
				debug!(target: "bft", "Invalid proposal: {:?}", e);
				return Box::new(future::ok(false));
			}
		};

		debug!(target: "bft", "Evaluating block proposal [number: {}; hash: {}; parent_hash: {}]",
			proposal.header().number(),
			<<C as AuthoringApi>::Block as BlockT>::Hash::from(proposal.header().hash()),
			proposal.header().parent_hash()
		);

		let vote_delays = {
			let now = Instant::now();

			// the duration until the given timestamp is current
			let proposed_timestamp = ::std::cmp::max(self.minimum_timestamp, proposal.timestamp());
			let timestamp_delay = if proposed_timestamp > current_timestamp {
				let delay_s = proposed_timestamp - current_timestamp;
				debug!(target: "bft", "Delaying evaluation of proposal for {} seconds", delay_s);
				Some(now + Duration::from_secs(delay_s))
			} else {
				None
			};

			match timestamp_delay {
				Some(duration) => future::Either::A(
					Delay::new(duration).map_err(|e| Error::from(ErrorKind::Timer(e)))
				),
				None => future::Either::B(future::ok(())),
			}
		};

		// refuse to vote if this block says a validator is offline that we
		// think isn't.
		let offline = proposal.noted_offline();
		if !self.offline.read().check_consistency(&self.validators[..], offline) {
			return Box::new(futures::empty());
		}

		// evaluate whether the block is actually valid.
		// TODO: is it better to delay this until the delays are finished?
		let evaluated = self.client
			.evaluate_block(&self.parent_id, unchecked_proposal.clone())
			.map_err(Into::into);

		let future = future::result(evaluated).and_then(move |good| {
			let end_result = future::ok(good);
			if good {
				// delay a "good" vote.
				future::Either::A(vote_delays.and_then(|_| end_result))
			} else {
				// don't delay a "bad" evaluation.
				future::Either::B(end_result)
			}
		});

		Box::new(future) as Box<_>
	}

	fn round_proposer(&self, round_number: usize, authorities: &[AuthorityId]) -> AuthorityId {
		let offset = self.primary_index(round_number, authorities.len());
		let proposer = authorities[offset].clone();
		trace!(target: "bft", "proposer for round {} is {}", round_number, proposer);

		proposer
	}

	fn import_misbehavior(&self, misbehavior: Vec<(AuthorityId, bft::Misbehavior<<<C as AuthoringApi>::Block as BlockT>::Hash>)>) {
		use rhododendron::Misbehavior as GenericMisbehavior;
		use runtime_primitives::bft::{MisbehaviorKind, MisbehaviorReport};
		use node_runtime::{Call, UncheckedExtrinsic, ConsensusCall};

		let local_id = self.local_key.public().0.into();
		let mut next_index = {
			let cur_index = self.transaction_pool.cull_and_get_pending(&BlockId::hash(self.parent_hash), |pending| pending
				.filter(|tx| tx.verified.sender == local_id)
				.last()
				.map(|tx| Ok(tx.verified.index()))
				.unwrap_or_else(|| AuthoringApi::index(self.client.as_ref(), &self.parent_id, local_id))
			);

			match cur_index {
				Ok(Ok(cur_index)) => cur_index + 1,
				Ok(Err(e)) => {
					warn!(target: "consensus", "Error computing next transaction index: {}", e);
					return;
				}
				Err(e) => {
					warn!(target: "consensus", "Error computing next transaction index: {}", e);
					return;
				}
			}
		};

		for (target, misbehavior) in misbehavior {
			let report = MisbehaviorReport {
				parent_hash: self.parent_hash.into(),
				parent_number: self.parent_number.as_(),
				target,
				misbehavior: match misbehavior {
					GenericMisbehavior::ProposeOutOfTurn(_, _, _) => continue,
					GenericMisbehavior::DoublePropose(_, _, _) => continue,
					GenericMisbehavior::DoublePrepare(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoublePrepare(round as u32, (h1.into(), s1.signature), (h2.into(), s2.signature)),
					GenericMisbehavior::DoubleCommit(round, (h1, s1), (h2, s2))
						=> MisbehaviorKind::BftDoubleCommit(round as u32, (h1.into(), s1.signature), (h2.into(), s2.signature)),
				}
			};
			let payload = (next_index, Call::Consensus(ConsensusCall::report_misbehavior(report)), Era::immortal(), self.client.genesis_hash());
			let signature = self.local_key.sign(&payload.encode()).into();
			next_index += 1;

			let local_id = self.local_key.public().0.into();
			let extrinsic = UncheckedExtrinsic {
				signature: Some((node_runtime::RawAddress::Id(local_id), signature, payload.0, Era::immortal())),
				function: payload.1,
			};
			let uxt: <<C as AuthoringApi>::Block as BlockT>::Extrinsic = Decode::decode(&mut extrinsic.encode().as_slice()).expect("Encoded extrinsic is valid");
			let hash = BlockId::<<C as AuthoringApi>::Block>::hash(self.parent_hash);
			self.transaction_pool.submit_one(&hash, uxt)
				.expect("locally signed extrinsic is valid; qed");
		}
	}

	fn on_round_end(&self, round_number: usize, was_proposed: bool) {
		let primary_validator = self.validators[
			self.primary_index(round_number, self.validators.len())
		];


		// alter the message based on whether we think the empty proposer was forced to skip the round.
		// this is determined by checking if our local validator would have been forced to skip the round.
		if !was_proposed {
			let public = ed25519::Public::from_raw(primary_validator.0);
			info!(
				"Potential Offline Validator: {} failed to propose during assigned slot: {}",
				public,
				round_number,
			);
		}

		self.offline.write().note_round_end(primary_validator, was_proposed);
	}
}

fn current_timestamp() -> Timestamp {
	time::SystemTime::now().duration_since(time::UNIX_EPOCH)
		.expect("now always later than unix epoch; qed")
		.as_secs()
}
