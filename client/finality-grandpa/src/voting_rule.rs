// This file is part of Substrate.

// Copyright (C) 2018-2021 Parity Technologies (UK) Ltd.
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

//! Handling custom voting rules for GRANDPA.
//!
//! This exposes the `VotingRule` trait used to implement arbitrary voting
//! restrictions that are taken into account by the GRANDPA environment when
//! selecting a finality target to vote on.

use std::sync::Arc;

use sc_client_api::blockchain::HeaderBackend;
use sp_runtime::generic::BlockId;
use sp_runtime::traits::{Block as BlockT, Header, NumberFor, One, Zero};

/// A trait for custom voting rules in GRANDPA.
pub trait VotingRule<Block, B>: Send + Sync where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	/// Restrict the given `current_target` vote, returning the block hash and
	/// number of the block to vote on, and `None` in case the vote should not
	/// be restricted. `base` is the block that we're basing our votes on in
	/// order to pick our target (e.g. last round estimate), and `best_target`
	/// is the initial best vote target before any vote rules were applied. When
	/// applying multiple `VotingRule`s both `base` and `best_target` should
	/// remain unchanged.
	///
	/// The contract of this interface requires that when restricting a vote, the
	/// returned value **must** be an ancestor of the given `current_target`,
	/// this also means that a variant must be maintained throughout the
	/// execution of voting rules wherein `current_target <= best_target`.
	fn restrict_vote(
		&self,
		backend: &B,
		base: &Block::Header,
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
		_base: &Block::Header,
		_best_target: &Block::Header,
		_current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		None
	}
}

/// A custom voting rule that guarantees that our vote is always behind the best
/// block by at least N blocks. In the best case our vote is exactly N blocks
/// behind the best block.
#[derive(Clone)]
pub struct BeforeBestBlockBy<N>(N);
impl<Block, B> VotingRule<Block, B> for BeforeBestBlockBy<NumberFor<Block>> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		backend: &B,
		_base: &Block::Header,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		use sp_arithmetic::traits::Saturating;

		if current_target.number().is_zero() {
			return None;
		}

		// find the target number restricted by this rule
		let target_number = best_target.number().saturating_sub(self.0);

		// our current target is already lower than this rule would restrict
		if target_number >= *current_target.number() {
			return None;
		}

		// find the block at the given target height
		find_target(
			backend,
			target_number,
			current_target,
		)
	}
}

/// A custom voting rule that limits votes towards 3/4 of the unfinalized chain,
/// using the given `base` and `best_target` to figure where the 3/4 target
/// should fall.
pub struct ThreeQuartersOfTheUnfinalizedChain;

impl<Block, B> VotingRule<Block, B> for ThreeQuartersOfTheUnfinalizedChain where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn restrict_vote(
		&self,
		backend: &B,
		base: &Block::Header,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		// target a vote towards 3/4 of the unfinalized chain (rounding up)
		let target_number = {
			let two = NumberFor::<Block>::one() + One::one();
			let three = two + One::one();
			let four = three + One::one();

			let diff = *best_target.number() - *base.number();
			let diff = ((diff * three) + two) / four;

			*base.number() + diff
		};

		// our current target is already lower than this rule would restrict
		if target_number >= *current_target.number() {
			return None;
		}

		// find the block at the given target height
		find_target(
			backend,
			target_number,
			current_target,
		)
	}
}

// walk backwards until we find the target block
fn find_target<Block, B>(
	backend: &B,
	target_number: NumberFor<Block>,
	current_header: &Block::Header,
) -> Option<(Block::Hash, NumberFor<Block>)> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	let mut target_hash = current_header.hash();
	let mut target_header = current_header.clone();

	loop {
		if *target_header.number() < target_number {
			unreachable!(
				"we are traversing backwards from a known block; \
				 blocks are stored contiguously; \
				 qed"
			);
		}

		if *target_header.number() == target_number {
			return Some((target_hash, target_number));
		}

		target_hash = *target_header.parent_hash();
		target_header = backend.header(BlockId::Hash(target_hash)).ok()?
			.expect("Header known to exist due to the existence of one of its descendents; qed");
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
		base: &Block::Header,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		let restricted_target = self.rules.iter().fold(
			current_target.clone(),
			|current_target, rule| {
				rule.restrict_vote(
					backend,
					base,
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

impl<Block, B> Default for VotingRulesBuilder<Block, B> where
	Block: BlockT,
	B: HeaderBackend<Block>,
{
	fn default() -> Self {
		VotingRulesBuilder::new()
			.add(BeforeBestBlockBy(2u32.into()))
			.add(ThreeQuartersOfTheUnfinalizedChain)
	}
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
		base: &Block::Header,
		best_target: &Block::Header,
		current_target: &Block::Header,
	) -> Option<(Block::Hash, NumberFor<Block>)> {
		(**self).restrict_vote(backend, base, best_target, current_target)
	}
}
