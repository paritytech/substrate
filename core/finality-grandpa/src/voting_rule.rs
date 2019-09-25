// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Handling custom voting rules for GRANDPA.
//!
//! This exposes the `VotingRule` trait used to implement arbitrary voting
//! restrictions that are taken into account by the GRANDPA environment when
//! selecting a finality target to vote on.

use std::sync::Arc;

use client::blockchain::HeaderBackend;
use sr_primitives::generic::BlockId;
use sr_primitives::traits::{Block as BlockT, Header, NumberFor, One, Zero};

/// A trait for custom voting rules in GRANDPA.
pub trait VotingRule<Block, B>: Send + Sync where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	/// Restrict the given `current_target` vote, returning the block hash and
	/// number of the block to vote on, and `None` in case the vote should not
	/// be restricted.
	///
	/// The contract of this interface requires that when restricting a vote,
	/// the returned value **must** be an ancestor of the given `current_target`.
	fn restrict_vote(
		&self,
		backend: &B,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)>;
}

impl<Block, B> VotingRule<Block, B> for () where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		_backend: &B,
		_best_target: &Block::Header,
		_current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		None
	}
}

/// A custom voting rule that guarantees that our vote is always behind the best
/// block, in the best case exactly one block behind it.
#[derive(Clone)]
pub struct AlwaysBehindBestBlock;
impl<Block, B> VotingRule<Block, B> for AlwaysBehindBestBlock where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		_backend: &B,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		debug_assert!(current_target.number() <= best_target.number());

		if current_target.number().is_zero() {
			return None;
		}

		if current_target.number() == best_target.number() {
			return Some((
				current_target.parent_hash().clone(),
				*current_target.number() - One::one(),
			));
		}

		None
	}
}

struct VotingRules<Block, B> {
	rules: Arc<Vec<Box<dyn VotingRule<Block, B>>>>,
}

impl<B, Block> Clone for VotingRules<B, Block> {
	fn clone(&self) -> Self {
		VotingRules {
			rules: self.rules.clone(),
		}
	}
}

impl<Block, B> VotingRule<Block, B> for VotingRules<Block, B> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		backend: &B,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		let restricted_target = self.rules.iter().fold(
			current_target.clone(),
			|current_target, rule| {
				rule.restrict_vote(
					backend,
					best_target,
					&current_target,
				)
					.and_then(|(hash, _)| backend.header(BlockId::Hash(hash)).ok())
					.and_then(std::convert::identity)
					.unwrap_or(current_target)
			},
		);

		let restricted_hash = restricted_target.hash();

		if restricted_hash != current_target.hash() {
			Some((restricted_hash, *restricted_target.number()))
		} else {
			None
		}
	}
}

/// A builder of a composite voting rule that applies a set of rules to
/// progressively restrict the vote.
pub struct VotingRulesBuilder<Block, B> {
	rules: Vec<Box<dyn VotingRule<Block, B>>>,
}

impl<Block, B> VotingRulesBuilder<Block, B> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	/// Return a new voting rule builder using the given backend.
	pub fn new() -> Self {
		VotingRulesBuilder {
			rules: Vec::new(),
		}
	}

	/// Add a new voting rule to the builder.
	pub fn add<R>(mut self, rule: R) -> Self where
		R: VotingRule<Block, B> + 'static,
	{
		self.rules.push(Box::new(rule));
		self
	}

	/// Add all given voting rules to the builder.
	pub fn add_all<I>(mut self, rules: I) -> Self where
		I: IntoIterator<Item=Box<dyn VotingRule<Block, B>>>,
	{
		self.rules.extend(rules);
		self
	}

	/// Return a new `VotingRule` that applies all of the previously added
	/// voting rules in-order.
	pub fn build(self) -> impl VotingRule<Block, B> + Clone {
		VotingRules {
			rules: Arc::new(self.rules),
		}
	}
}

impl<Block, B> VotingRule<Block, B> for Box<dyn VotingRule<Block, B>> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		backend: &B,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		(**self).restrict_vote(backend, best_target, current_target)
	}
}
