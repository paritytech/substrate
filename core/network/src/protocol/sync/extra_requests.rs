// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

use client::error::Error as ClientError;
use crate::protocol::sync::{PeerSync, PeerSyncState};
use fork_tree::ForkTree;
use libp2p::PeerId;
use log::warn;
use runtime_primitives::traits::{Block as BlockT, NumberFor};
use std::collections::{HashMap, HashSet, VecDeque};
use std::time::{Duration, Instant};

// Time to wait before trying to get the same extra data from the same peer.
const EXTRA_RETRY_WAIT: Duration = Duration::from_secs(10);

/// Pending extra data request for the given block (hash and number).
pub(crate) type ExtraRequest<B> = (<B as BlockT>::Hash, NumberFor<B>);

/// Manages pending block extra data (e.g. justification) requests.
///
/// Multiple extras may be requested for competing forks, or for the same branch
/// at different (increasing) heights. This structure will guarantee that extras
/// are fetched in-order, and that obsolete changes are pruned (when finalizing a
/// competing fork).
#[derive(Debug)]
pub(crate) struct ExtraRequests<B: BlockT> {
	tree: ForkTree<B::Hash, NumberFor<B>, ()>,
	/// requests which have been queued for later processing
	pending_requests: VecDeque<ExtraRequest<B>>,
	/// requests which are currently underway to some peer
	active_requests: HashMap<PeerId, ExtraRequest<B>>,
	/// previous requests without response
	failed_requests: HashMap<ExtraRequest<B>, Vec<(PeerId, Instant)>>,
	/// successful requests
	importing_requests: HashSet<ExtraRequest<B>>,
}

impl<B: BlockT> ExtraRequests<B> {
	pub(crate) fn new() -> Self {
		ExtraRequests {
			tree: ForkTree::new(),
			pending_requests: VecDeque::new(),
			active_requests: HashMap::new(),
			failed_requests: HashMap::new(),
			importing_requests: HashSet::new(),
		}
	}

	/// Reset all state as if returned from `new`.
	pub(crate) fn reset(&mut self) {
		self.tree = ForkTree::new();
		self.pending_requests.clear();
		self.active_requests.clear();
		self.failed_requests.clear();
	}

	/// Returns an iterator-like struct that yields peers which extra
	/// requests can be sent to.
	pub(crate) fn matcher(&mut self) -> Matcher<B> {
		Matcher::new(self)
	}

	/// Queue an extra data request to be considered by the `Matcher`.
	pub(crate) fn schedule<F>(&mut self, request: ExtraRequest<B>, is_descendent_of: F)
		where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError>
	{
		match self.tree.import(request.0, request.1, (), &is_descendent_of) {
			Ok(true) => {
				// this is a new root so we add it to the current `pending_requests`
				self.pending_requests.push_back((request.0, request.1))
			}
			Err(err) => {
				warn!(target: "sync", "Failed to insert request {:?} into tree: {:?}", request, err);
				return
			}
			_ => ()
		}
	}

	/// Retry any pending request if a peer disconnected.
	pub(crate) fn peer_disconnected(&mut self, who: &PeerId) {
		if let Some(request) = self.active_requests.remove(who) {
			self.pending_requests.push_front(request)
		}
	}

	/// Processes the response for the request previously sent to the given peer.
	pub(crate) fn on_response<R>(&mut self, who: PeerId, resp: Option<R>) -> Option<(PeerId, B::Hash, NumberFor<B>, R)> {
		// we assume that the request maps to the given response, this is
		// currently enforced by the outer network protocol before passing on
		// messages to chain sync.
		if let Some(request) = self.active_requests.remove(&who) {
			if let Some(r) = resp {
				self.importing_requests.insert(request);
				return Some((who, request.0, request.1, r))
			}
			self.failed_requests.entry(request).or_insert(Vec::new()).push((who, Instant::now()));
			self.pending_requests.push_front(request);
		}
		None
	}

	/// Removes any pending extra requests for blocks lower than the given best finalized.
	pub(crate) fn on_block_finalized<F>(
		&mut self,
		best_finalized_hash: &B::Hash,
		best_finalized_number: NumberFor<B>,
		is_descendent_of: F
	) -> Result<(), fork_tree::Error<ClientError>>
		where F: Fn(&B::Hash, &B::Hash) -> Result<bool, ClientError>
	{
		let request = (*best_finalized_hash, best_finalized_number);

		if self.try_finalize_root::<()>(request, Ok(request), false) {
			return Ok(())
		}

		self.tree.finalize(best_finalized_hash, best_finalized_number, &is_descendent_of)?;

		let roots = self.tree.roots().collect::<HashSet<_>>();

		self.pending_requests.retain(|(h, n)| roots.contains(&(h, n, &())));
		self.active_requests.retain(|_, (h, n)| roots.contains(&(h, n, &())));
		self.failed_requests.retain(|(h, n), _| roots.contains(&(h, n, &())));

		Ok(())
	}

	/// Try to finalize pending root.
	///
	/// Returns true if import of this request has been scheduled.
	pub(crate) fn try_finalize_root<E>(
		&mut self,
		request: ExtraRequest<B>,
		result: Result<ExtraRequest<B>, E>,
		reschedule_on_failure: bool
	) -> bool
	{
		if !self.importing_requests.remove(&request) {
			return false
		}

		let (finalized_hash, finalized_number) = match result {
			Ok(req) => (req.0, req.1),
			Err(_) => {
				if reschedule_on_failure {
					self.pending_requests.push_front(request);
				}
				return true
			}
		};

		if self.tree.finalize_root(&finalized_hash).is_none() {
			warn!(target: "sync", "Imported {:?} {:?} which isn't a root in the tree: {:?}",
				finalized_hash,
				finalized_number,
				self.tree.roots().collect::<Vec<_>>()
			);
			return true
		}

		self.failed_requests.clear();
		self.active_requests.clear();
		self.pending_requests.clear();
		self.pending_requests.extend(self.tree.roots().map(|(&h, &n, _)| (h, n)));

		true
	}
}

/// Matches peers with pending extra requests.
#[derive(Debug)]
pub(crate) struct Matcher<'a, B: BlockT> {
	/// Length of pending requests collection.
	/// Used to ensure we do not loop more than once over all pending requests.
	remaining: usize,
	extras: &'a mut ExtraRequests<B>
}

impl<'a, B: BlockT> Matcher<'a, B> {
	fn new(extras: &'a mut ExtraRequests<B>) -> Self {
		Matcher {
			remaining: extras.pending_requests.len(),
			extras
		}
	}

	/// Finds a peer to which a pending request can be sent.
	///
	/// Peers are filtered according to the current known best block (i.e. we won't
	/// send an extra request for block #10 to a peer at block #2), and we also
	/// throttle requests to the same peer if a previous request yielded no results.
	///
	/// This method returns as soon as it finds a peer that should be able to answer
	/// our request. If no request is pending or no peer can handle it, `None` is
	/// returned instead.
	///
	/// # Note
	///
	/// The returned `PeerId` (if any) is guaranteed to come from the given `peers`
	/// argument.
	pub(crate) fn next(&mut self, peers: &HashMap<PeerId, PeerSync<B>>) -> Option<(PeerId, ExtraRequest<B>)> {
		if self.remaining == 0 {
			return None
		}

		// clean up previously failed requests so we can retry again
		for requests in self.extras.failed_requests.values_mut() {
			requests.retain(|(_, instant)| instant.elapsed() < EXTRA_RETRY_WAIT);
		}

		while let Some(request) = self.extras.pending_requests.pop_front() {
			for (peer, sync) in peers.iter().filter(|(_, sync)| sync.state == PeerSyncState::Available) {
				// only ask peers that have synced at least up to the block number that we're asking the extra for
				if sync.best_number < request.1 {
					continue
				}
				// don't request to any peers that already have pending requests
				if self.extras.active_requests.contains_key(peer) {
					continue
				}
				// only ask if the same request has not failed for this peer before
				if self.extras.failed_requests.get(&request).map(|rr| rr.iter().any(|i| &i.0 == peer)).unwrap_or(false) {
					continue
				}
				self.extras.active_requests.insert(peer.clone(), request);
				return Some((peer.clone(), request))
			}

			self.extras.pending_requests.push_back(request);
			self.remaining -= 1;

			if self.remaining == 0 {
				break
			}
		}

		None
	}
}

#[cfg(test)]
mod tests {
	use crate::protocol::sync::PeerSync;
	use client::error::Error as ClientError;
	use quickcheck::{Arbitrary, Gen, QuickCheck, StdThreadGen};
	use rand::Rng;
	use std::collections::{HashMap, HashSet};
	use super::*;
	use test_client::runtime::{Block, BlockNumber, Hash};

	#[test]
	fn requests_are_processed_in_order() {
		fn property(mut peers: ArbitraryPeers) {
			let mut requests = ExtraRequests::<Block>::new();

			let num_peers_available = peers.0.values()
				.filter(|s| s.state == PeerSyncState::Available).count();

			for i in 0 .. num_peers_available {
				requests.schedule((Hash::random(), i as u64), |a, b| Ok(a[0] >= b[0]))
			}

			let pending = requests.pending_requests.clone();
			let mut m = requests.matcher();

			for p in &pending {
				let (peer, r) = m.next(&peers.0).unwrap();
				assert_eq!(p, &r);
				peers.0.get_mut(&peer).unwrap().state = PeerSyncState::DownloadingJustification(r.0);
			}
		}

		QuickCheck::with_gen(StdThreadGen::new(19))
			.quickcheck(property as fn(ArbitraryPeers))
	}

	#[test]
	fn new_roots_schedule_new_request() {
		fn property(data: Vec<BlockNumber>) {
			let mut requests = ExtraRequests::<Block>::new();
			for (i, number) in data.into_iter().enumerate() {
				let hash = [i as u8; 32].into();
				let pending = requests.pending_requests.len();
				let is_root = requests.tree.roots().any(|(&h, &n, _)| hash == h && number == n);
				requests.schedule((hash, number), |a, b| Ok(a[0] >= b[0]));
				if !is_root {
					assert_eq!(1 + pending, requests.pending_requests.len())
				}
			}
		}
		QuickCheck::new().quickcheck(property as fn(Vec<BlockNumber>))
	}

	#[test]
	fn disconnecting_implies_rescheduling() {
		fn property(mut peers: ArbitraryPeers) -> bool {
			let mut requests = ExtraRequests::<Block>::new();

			let num_peers_available = peers.0.values()
				.filter(|s| s.state == PeerSyncState::Available).count();

			for i in 0 .. num_peers_available {
				requests.schedule((Hash::random(), i as u64), |a, b| Ok(a[0] >= b[0]))
			}

			let mut m = requests.matcher();
			while let Some((peer, r)) = m.next(&peers.0) {
				peers.0.get_mut(&peer).unwrap().state = PeerSyncState::DownloadingJustification(r.0);
			}

			assert!(requests.pending_requests.is_empty());

			let active_peers = requests.active_requests.keys().cloned().collect::<Vec<_>>();
			let previously_active = requests.active_requests.values().cloned().collect::<HashSet<_>>();

			for peer in &active_peers {
				requests.peer_disconnected(peer)
			}

			assert!(requests.active_requests.is_empty());

			previously_active == requests.pending_requests.iter().cloned().collect::<HashSet<_>>()
		}

		QuickCheck::with_gen(StdThreadGen::new(19))
			.quickcheck(property as fn(ArbitraryPeers) -> bool)
	}

	#[test]
	fn no_response_reschedules() {
		fn property(mut peers: ArbitraryPeers) {
			let mut requests = ExtraRequests::<Block>::new();

			let num_peers_available = peers.0.values()
				.filter(|s| s.state == PeerSyncState::Available).count();

			for i in 0 .. num_peers_available {
				requests.schedule((Hash::random(), i as u64), |a, b| Ok(a[0] >= b[0]))
			}

			let mut m = requests.matcher();
			while let Some((peer, r)) = m.next(&peers.0) {
				peers.0.get_mut(&peer).unwrap().state = PeerSyncState::DownloadingJustification(r.0);
			}

			let active = requests.active_requests.iter().map(|(p, &r)| (p.clone(), r)).collect::<Vec<_>>();

			for (peer, req) in &active {
				assert!(requests.failed_requests.get(req).is_none());
				assert!(!requests.pending_requests.contains(req));
				assert!(requests.on_response::<()>(peer.clone(), None).is_none());
				assert!(requests.pending_requests.contains(req));
				assert_eq!(1, requests.failed_requests.get(req).unwrap().iter().filter(|(p, _)| p == peer).count())
			}
		}

		QuickCheck::with_gen(StdThreadGen::new(19))
			.quickcheck(property as fn(ArbitraryPeers))
	}

	#[test]
	fn request_is_rescheduled_when_earlier_block_is_finalized() {
		let _ = ::env_logger::try_init();

		let mut finality_proofs = ExtraRequests::<Block>::new();

		let hash4 = [4; 32].into();
		let hash5 = [5; 32].into();
		let hash6 = [6; 32].into();
		let hash7 = [7; 32].into();

		fn is_descendent_of(base: &Hash, target: &Hash) -> Result<bool, ClientError> {
			Ok(target[0] >= base[0])
		}

		// make #4 last finalized block
		finality_proofs.tree.import(hash4, 4, (), &is_descendent_of).unwrap();
		finality_proofs.tree.finalize_root(&hash4);

		// schedule request for #6
		finality_proofs.schedule((hash6, 6), is_descendent_of);

		// receive finality proof for #5
		finality_proofs.importing_requests.insert((hash6, 6));
		finality_proofs.on_block_finalized(&hash5, 5, is_descendent_of).unwrap();
		finality_proofs.try_finalize_root::<()>((hash6, 6), Ok((hash5, 5)), true);

		// ensure that request for #6 is still pending
		assert_eq!(finality_proofs.pending_requests.iter().collect::<Vec<_>>(), vec![&(hash6, 6)]);

		// receive finality proof for #7
		finality_proofs.importing_requests.insert((hash6, 6));
		finality_proofs.on_block_finalized(&hash6, 6, is_descendent_of).unwrap();
		finality_proofs.on_block_finalized(&hash7, 7, is_descendent_of).unwrap();
		finality_proofs.try_finalize_root::<()>((hash6, 6), Ok((hash7, 7)), true);

		// ensure that there's no request for #6
		assert_eq!(finality_proofs.pending_requests.iter().collect::<Vec<_>>(), Vec::<&(Hash, u64)>::new());
	}

	// Some Arbitrary instances to allow easy construction of random peer sets:

	#[derive(Debug, Clone)]
	struct ArbitraryPeerSyncState(PeerSyncState<Block>);

	impl Arbitrary for ArbitraryPeerSyncState {
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			let s = match g.gen::<u8>() % 5 {
				0 => PeerSyncState::Available,
				// TODO: 1 => PeerSyncState::AncestorSearch(g.gen(), AncestorSearchState<B>),
				1 => PeerSyncState::DownloadingNew(g.gen::<BlockNumber>()),
				2 => PeerSyncState::DownloadingStale(Hash::random()),
				3 => PeerSyncState::DownloadingJustification(Hash::random()),
				_ => PeerSyncState::DownloadingFinalityProof(Hash::random())
			};
			ArbitraryPeerSyncState(s)
		}
	}

	#[derive(Debug, Clone)]
	struct ArbitraryPeerSync(PeerSync<Block>);

	impl Arbitrary for ArbitraryPeerSync {
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			let ps = PeerSync {
				common_number: g.gen(),
				best_hash: Hash::random(),
				best_number: g.gen(),
				state: ArbitraryPeerSyncState::arbitrary(g).0,
				recently_announced: Default::default()
			};
			ArbitraryPeerSync(ps)
		}
	}

	#[derive(Debug, Clone)]
	struct ArbitraryPeers(HashMap<PeerId, PeerSync<Block>>);

	impl Arbitrary for ArbitraryPeers {
		fn arbitrary<G: Gen>(g: &mut G) -> Self {
			let mut peers = HashMap::with_capacity(g.size());
			for _ in 0 .. g.size() {
				peers.insert(PeerId::random(), ArbitraryPeerSync::arbitrary(g).0);
			}
			ArbitraryPeers(peers)
		}
	}

}
