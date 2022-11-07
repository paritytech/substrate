// This file is part of Substrate.

// Copyright (C) 2022 Parity Technologies (UK) Ltd.
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

//! Substrate transaction pool implementation.

use sc_transaction_pool_api::ChainEvent;
use sp_blockchain::TreeRoute;
use sp_runtime::traits::Block as BlockT;

/// Helper struct for keeping track of the current state of processed new best
/// block and finalized events. The main purpose of keeping track of this state
/// is to figure out if a transaction pool enactment is needed or not.
///
/// Given the following chain:
///
///   B1-C1-D1-E1
///  /
/// A
///  \
///   B2-C2-D2-E2
///
/// Some scenarios and expected behavior for sequence of `NewBestBlock` (`nbb`) and `Finalized`
/// (`f`) events:
///
/// - `nbb(C1)`, `f(C1)` -> false (enactment was already performed in `nbb(C1))`
/// - `f(C1)`, `nbb(C1)` -> false (enactment was already performed in `f(C1))`
/// - `f(C1)`, `nbb(D2)` -> false (enactment was already performed in `f(C1)`,
/// we should not retract finalized block)
/// - `f(C1)`, `f(C2)`, `nbb(C1)` -> false
/// - `nbb(C1)`, `nbb(C2)` -> true (switching fork is OK)
/// - `nbb(B1)`, `nbb(B2)` -> true
/// - `nbb(B1)`, `nbb(C1)`, `f(C1)` -> false (enactment was already performed in `nbb(B1)`)
/// - `nbb(C1)`, `f(B1)` -> false (enactment was already performed in `nbb(B2)`)
pub struct EnactmentState<Block>
where
	Block: BlockT,
{
	recent_best_block: Block::Hash,
	recent_finalized_block: Block::Hash,
}

impl<Block> EnactmentState<Block>
where
	Block: BlockT,
{
	/// Returns a new `EnactmentState` initialized with the given parameters.
	pub fn new(recent_best_block: Block::Hash, recent_finalized_block: Block::Hash) -> Self {
		EnactmentState { recent_best_block, recent_finalized_block }
	}

	/// Returns the recently finalized block.
	pub fn recent_finalized_block(&self) -> Block::Hash {
		self.recent_finalized_block
	}

	/// Updates the state according to the given `ChainEvent`, returning
	/// `Some(tree_route)` with a tree route including the blocks that need to
	/// be enacted/retracted. If no enactment is needed then `None` is returned.
	pub fn update<F>(
		&mut self,
		event: &ChainEvent<Block>,
		tree_route: &F,
	) -> Result<Option<TreeRoute<Block>>, String>
	where
		F: Fn(Block::Hash, Block::Hash) -> Result<TreeRoute<Block>, String>,
	{
		let (new_hash, finalized) = match event {
			ChainEvent::NewBestBlock { hash, .. } => (*hash, false),
			ChainEvent::Finalized { hash, .. } => (*hash, true),
		};

		// block was already finalized
		if self.recent_finalized_block == new_hash {
			log::debug!(target: "txpool", "handle_enactment: block already finalized");
			return Ok(None)
		}

		// compute actual tree route from best_block to notified block, and use
		// it instead of tree_route provided with event
		let tree_route = tree_route(self.recent_best_block, new_hash)?;

		log::debug!(
			target: "txpool",
			"resolve hash:{:?} finalized:{:?} tree_route:{:?} best_block:{:?} finalized_block:{:?}",
			new_hash, finalized, tree_route, self.recent_best_block, self.recent_finalized_block
		);

		// check if recently finalized block is on retracted path. this could be
		// happening if we first received a finalization event and then a new
		// best event for some old stale best head.
		if tree_route.retracted().iter().any(|x| x.hash == self.recent_finalized_block) {
			log::debug!(
				target: "txpool",
				"Recently finalized block {} would be retracted by ChainEvent {}, skipping",
				self.recent_finalized_block, new_hash
			);
			return Ok(None)
		}

		if finalized {
			self.recent_finalized_block = new_hash;

			// if there are no enacted blocks in best_block -> hash tree_route,
			// it means that block being finalized was already enacted (this
			// case also covers best_block == new_hash), recent_best_block
			// remains valid.
			if tree_route.enacted().is_empty() {
				log::trace!(
					target: "txpool",
					"handle_enactment: no newly enacted blocks since recent best block"
				);
				return Ok(None)
			}

			// otherwise enacted finalized block becomes best block...
		}

		self.recent_best_block = new_hash;

		Ok(Some(tree_route))
	}

	/// Forces update of the state according to the given `ChainEvent`. Intended to be used as a
	/// fallback when tree_route cannot be computed.
	pub fn force_update(&mut self, event: &ChainEvent<Block>) {
		match event {
			ChainEvent::NewBestBlock { hash, .. } => self.recent_best_block = *hash,
			ChainEvent::Finalized { hash, .. } => self.recent_finalized_block = *hash,
		};
		log::debug!(target: "txpool", "forced update: {:?}, {:?}", self.recent_best_block, self.recent_finalized_block);
	}
}

#[cfg(test)]
mod enactment_state_tests {
	use super::EnactmentState;
	use sc_transaction_pool_api::ChainEvent;
	use sp_blockchain::{HashAndNumber, TreeRoute};
	use std::sync::Arc;
	use substrate_test_runtime_client::runtime::{Block, Hash};

	// some helpers for convenient blocks' hash naming
	fn a() -> HashAndNumber<Block> {
		HashAndNumber { number: 1, hash: Hash::from([0xAA; 32]) }
	}
	fn b1() -> HashAndNumber<Block> {
		HashAndNumber { number: 2, hash: Hash::from([0xB1; 32]) }
	}
	fn c1() -> HashAndNumber<Block> {
		HashAndNumber { number: 3, hash: Hash::from([0xC1; 32]) }
	}
	fn d1() -> HashAndNumber<Block> {
		HashAndNumber { number: 4, hash: Hash::from([0xD1; 32]) }
	}
	fn e1() -> HashAndNumber<Block> {
		HashAndNumber { number: 5, hash: Hash::from([0xE1; 32]) }
	}
	fn b2() -> HashAndNumber<Block> {
		HashAndNumber { number: 2, hash: Hash::from([0xB2; 32]) }
	}
	fn c2() -> HashAndNumber<Block> {
		HashAndNumber { number: 3, hash: Hash::from([0xC2; 32]) }
	}
	fn d2() -> HashAndNumber<Block> {
		HashAndNumber { number: 4, hash: Hash::from([0xD2; 32]) }
	}
	fn e2() -> HashAndNumber<Block> {
		HashAndNumber { number: 5, hash: Hash::from([0xE2; 32]) }
	}

	/// mock tree_route computing function for simple two-forks chain
	fn tree_route(from: Hash, to: Hash) -> Result<TreeRoute<Block>, String> {
		let chain = vec![e1(), d1(), c1(), b1(), a(), b2(), c2(), d2(), e2()];
		let pivot = 4_usize;

		let from = chain
			.iter()
			.position(|bn| bn.hash == from)
			.ok_or("existing block should be given")?;
		let to = chain
			.iter()
			.position(|bn| bn.hash == to)
			.ok_or("existing block should be given")?;

		//    B1-C1-D1-E1
		//   /
		//  A
		//   \
		//    B2-C2-D2-E2
		//
		//  [E1 D1 C1 B1 A B2 C2 D2 E2]

		let vec: Vec<HashAndNumber<Block>> = if from < to {
			chain.into_iter().skip(from).take(to - from + 1).collect()
		} else {
			chain.into_iter().skip(to).take(from - to + 1).rev().collect()
		};

		let pivot = if from <= pivot && to <= pivot {
			if from < to {
				to - from
			} else {
				0
			}
		} else if from >= pivot && to >= pivot {
			if from < to {
				0
			} else {
				from - to
			}
		} else {
			if from < to {
				pivot - from
			} else {
				from - pivot
			}
		};

		Ok(TreeRoute::new(vec, pivot))
	}

	mod mock_tree_route_tests {
		use super::*;

		/// asserts that tree routes are equal
		fn assert_treeroute_eq(expected: TreeRoute<Block>, result: TreeRoute<Block>) {
			assert_eq!(result.common_block().hash, expected.common_block().hash);
			assert_eq!(result.enacted().len(), expected.enacted().len());
			assert_eq!(result.retracted().len(), expected.retracted().len());
			assert!(result
				.enacted()
				.iter()
				.zip(expected.enacted().iter())
				.all(|(a, b)| a.hash == b.hash));
			assert!(result
				.retracted()
				.iter()
				.zip(expected.retracted().iter())
				.all(|(a, b)| a.hash == b.hash));
		}

		// some tests for mock tree_route function
		#[test]
		fn tree_route_mock_test_01() {
			let result = tree_route(b1().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), a()], 1);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_02() {
			let result = tree_route(a().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a(), b1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_03() {
			let result = tree_route(a().hash, c2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a(), b2(), c2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_04() {
			let result = tree_route(e2().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![e2(), d2(), c2(), b2(), a()], 4);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_05() {
			let result = tree_route(d1().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d1(), c1(), b1()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_06() {
			let result = tree_route(d2().hash, b2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d2(), c2(), b2()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_07() {
			let result = tree_route(b1().hash, d1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), c1(), d1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_08() {
			let result = tree_route(b2().hash, d2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b2(), c2(), d2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_09() {
			let result = tree_route(e2().hash, e1().hash).expect("tree route exists");
			let expected =
				TreeRoute::new(vec![e2(), d2(), c2(), b2(), a(), b1(), c1(), d1(), e1()], 4);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_10() {
			let result = tree_route(e1().hash, e2().hash).expect("tree route exists");
			let expected =
				TreeRoute::new(vec![e1(), d1(), c1(), b1(), a(), b2(), c2(), d2(), e2()], 4);
			assert_treeroute_eq(result, expected);
		}
		#[test]
		fn tree_route_mock_test_11() {
			let result = tree_route(b1().hash, c2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1(), a(), b2(), c2()], 1);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_12() {
			let result = tree_route(d2().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![d2(), c2(), b2(), a(), b1()], 3);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_13() {
			let result = tree_route(c2().hash, e1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![c2(), b2(), a(), b1(), c1(), d1(), e1()], 2);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_14() {
			let result = tree_route(b1().hash, b1().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b1()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_15() {
			let result = tree_route(b2().hash, b2().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![b2()], 0);
			assert_treeroute_eq(result, expected);
		}

		#[test]
		fn tree_route_mock_test_16() {
			let result = tree_route(a().hash, a().hash).expect("tree route exists");
			let expected = TreeRoute::new(vec![a()], 0);
			assert_treeroute_eq(result, expected);
		}
	}

	fn trigger_new_best_block(
		state: &mut EnactmentState<Block>,
		from: HashAndNumber<Block>,
		acted_on: HashAndNumber<Block>,
	) -> bool {
		let (from, acted_on) = (from.hash, acted_on.hash);

		let event_tree_route = tree_route(from, acted_on).expect("Tree route exists");

		state
			.update(
				&ChainEvent::NewBestBlock {
					hash: acted_on,
					tree_route: Some(Arc::new(event_tree_route)),
				},
				&tree_route,
			)
			.unwrap()
			.is_some()
	}

	fn trigger_finalized(
		state: &mut EnactmentState<Block>,
		from: HashAndNumber<Block>,
		acted_on: HashAndNumber<Block>,
	) -> bool {
		let (from, acted_on) = (from.hash, acted_on.hash);

		let v = tree_route(from, acted_on)
			.expect("Tree route exists")
			.enacted()
			.iter()
			.map(|h| h.hash)
			.collect::<Vec<_>>();

		state
			.update(&ChainEvent::Finalized { hash: acted_on, tree_route: v.into() }, &tree_route)
			.unwrap()
			.is_some()
	}

	fn assert_es_eq(
		es: &EnactmentState<Block>,
		expected_best_block: HashAndNumber<Block>,
		expected_finalized_block: HashAndNumber<Block>,
	) {
		assert_eq!(es.recent_best_block, expected_best_block.hash);
		assert_eq!(es.recent_finalized_block, expected_finalized_block.hash);
	}

	#[test]
	fn test_enactment_helper() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		//   B1-C1-D1-E1
		//  /
		// A
		//  \
		//   B2-C2-D2-E2

		let result = trigger_new_best_block(&mut es, a(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), a());

		let result = trigger_new_best_block(&mut es, d1(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), d2());
		assert!(result);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, d2(), e1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), b2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), d2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_finalized(&mut es, a(), d2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), c2());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, d2(), d2());

		let result = trigger_new_best_block(&mut es, d2(), e2());
		assert!(result);
		assert_es_eq(&es, e2(), d2());

		let result = trigger_finalized(&mut es, d2(), e2());
		assert_eq!(result, false);
		assert_es_eq(&es, e2(), e2());
	}

	#[test]
	fn test_enactment_helper_2() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), b1());
		assert!(result);
		assert_es_eq(&es, b1(), a());

		let result = trigger_new_best_block(&mut es, b1(), c1());
		assert!(result);
		assert_es_eq(&es, c1(), a());

		let result = trigger_new_best_block(&mut es, c1(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), a());

		let result = trigger_new_best_block(&mut es, d1(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), c1());

		let result = trigger_finalized(&mut es, c1(), e1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_3() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), a());

		let result = trigger_finalized(&mut es, a(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), b1());
	}

	#[test]
	fn test_enactment_helper_4() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_finalized(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), e1());

		let result = trigger_finalized(&mut es, e1(), b1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_5() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		//   B1-C1-D1-E1
		//  /
		// A
		//  \
		//   B2-C2-D2-E2

		let result = trigger_finalized(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), e1());

		let result = trigger_finalized(&mut es, e1(), e2());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), e1());
	}

	#[test]
	fn test_enactment_helper_6() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		// A-B1-C1-D1-E1

		let result = trigger_new_best_block(&mut es, a(), b1());
		assert!(result);
		assert_es_eq(&es, b1(), a());

		let result = trigger_finalized(&mut es, a(), d1());
		assert!(result);
		assert_es_eq(&es, d1(), d1());

		let result = trigger_new_best_block(&mut es, a(), e1());
		assert!(result);
		assert_es_eq(&es, e1(), d1());

		let result = trigger_new_best_block(&mut es, a(), c1());
		assert_eq!(result, false);
		assert_es_eq(&es, e1(), d1());
	}

	#[test]
	fn test_enactment_forced_update_best_block() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		es.force_update(&ChainEvent::NewBestBlock { hash: b1().hash, tree_route: None });
		assert_es_eq(&es, b1(), a());
	}

	#[test]
	fn test_enactment_forced_update_finalize() {
		sp_tracing::try_init_simple();
		let mut es = EnactmentState::new(a().hash, a().hash);

		es.force_update(&ChainEvent::Finalized { hash: b1().hash, tree_route: Arc::from([]) });
		assert_es_eq(&es, a(), b1());
	}
}
