// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Gossip and politeness for polite-grandpa.
//!
//! This module implements the following message types:
//! #### Neighbor Packet
//!
//! The neighbor packet is sent to only our neighbors. It contains this information
//!
//!   - Current Round
//!   - Current voter set ID
//!   - Last finalized hash from commit messages.
//!
//! If a peer is at a given voter set, it is impolite to send messages from
//! an earlier voter set. It is extremely impolite to send messages
//! from a future voter set. "future-set" messages can be dropped and ignored.
//!
//! If a peer is at round r, is impolite to send messages about r-2 or earlier and extremely
//! impolite to send messages about r+1 or later. "future-round" messages can
//!  be dropped and ignored.
//!
//! It is impolite to send a neighbor packet which moves backwards in protocol state.
//!
//! This is beneficial if it conveys some progress in the protocol state of the peer.
//!
//! #### Prevote / Precommit
//!
//! These are votes within a round. Noting that we receive these messages
//! from our peers who are not necessarily voters, we have to account the benefit
//! based on what they might have seen.
//!
//! #### Propose
//!
//! This is a broadcast by a known voter of the last-round estimate.
//!
//! #### Commit
//!
//! These are used to announce past agreement of finality.
//!
//! It is impolite to send commits which are earlier than the last commit
//! sent. It is especially impolite to send commits which are invalid, or from
//! a different Set ID than the receiving peer has indicated.
//!
//! Sending a commit is polite when it may finalize something that the receiving peer
//! was not aware of.
//!
//! #### Catch Up
//!
//! These allow a peer to request another peer, which they perceive to be in a
//! later round, to provide all the votes necessary to complete a given round
//! `R`.
//!
//! It is impolite to send a catch up request for a round `R` to a peer whose
//! announced view is behind `R`. It is also impolite to send a catch up request
//! to a peer in a new different Set ID.
//!
//! The logic for issuing and tracking pending catch up requests is implemented
//! in the `GossipValidator`. A catch up request is issued anytime we see a
//! neighbor packet from a peer at a round `CATCH_UP_THRESHOLD` higher than at
//! we are.
//!
//! ## Expiration
//!
//! We keep some amount of recent rounds' messages, but do not accept new ones from rounds
//! older than our current_round - 1.
//!
//! ## Message Validation
//!
//! We only send polite messages to peers,

use ahash::{AHashMap, AHashSet};
use log::{debug, trace};
use parity_scale_codec::{Decode, Encode};
use prometheus_endpoint::{register, CounterVec, Opts, PrometheusError, Registry, U64};
use rand::seq::SliceRandom;
use sc_network::{PeerId, ReputationChange};
use sc_network_common::protocol::event::ObservedRole;
use sc_network_gossip::{MessageIntent, ValidatorContext};
use sc_telemetry::{telemetry, TelemetryHandle, CONSENSUS_DEBUG};
use sc_utils::mpsc::{tracing_unbounded, TracingUnboundedReceiver, TracingUnboundedSender};
use sp_finality_grandpa::AuthorityId;
use sp_runtime::traits::{Block as BlockT, NumberFor, Zero};

use super::{benefit, cost, Round, SetId};
use crate::{environment, CatchUp, CompactCommit, SignedMessage};

use std::{
	collections::{HashSet, VecDeque},
	time::{Duration, Instant},
};

const REBROADCAST_AFTER: Duration = Duration::from_secs(60 * 5);
const CATCH_UP_REQUEST_TIMEOUT: Duration = Duration::from_secs(45);
const CATCH_UP_PROCESS_TIMEOUT: Duration = Duration::from_secs(30);
/// Maximum number of rounds we are behind a peer before issuing a
/// catch up request.
const CATCH_UP_THRESHOLD: u64 = 2;

/// The total round duration measured in periods of gossip duration:
/// 2 gossip durations for prevote timer
/// 2 gossip durations for precommit timer
/// 1 gossip duration for precommits to spread
const ROUND_DURATION: u32 = 5;

/// The period, measured in rounds, since the latest round start, after which we will start
/// propagating gossip messages to more nodes than just the lucky ones.
const PROPAGATION_SOME: f32 = 1.5;

/// The period, measured in rounds, since the latest round start, after which we will start
/// propagating gossip messages to all the nodes we are connected to.
const PROPAGATION_ALL: f32 = 3.0;

/// Assuming a network of 3000 nodes, using a fanout of 4, after about 6 iterations
/// of gossip a message has very likely reached all nodes on the network (`log4(3000)`).
const LUCKY_PEERS: usize = 4;

type Report = (PeerId, ReputationChange);

/// An outcome of examining a message.
#[derive(Debug, PartialEq, Clone, Copy)]
enum Consider {
	/// Accept the message.
	Accept,
	/// Message is too early. Reject.
	RejectPast,
	/// Message is from the future. Reject.
	RejectFuture,
	/// Message cannot be evaluated. Reject.
	RejectOutOfScope,
}

/// A view of protocol state.
#[derive(Debug)]
struct View<N> {
	round: Round,           // the current round we are at.
	set_id: SetId,          // the current voter set id.
	last_commit: Option<N>, // commit-finalized block height, if any.
}

impl<N> Default for View<N> {
	fn default() -> Self {
		View { round: Round(1), set_id: SetId(0), last_commit: None }
	}
}

impl<N: Ord> View<N> {
	/// Consider a round and set ID combination under a current view.
	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		// only from current set
		if set_id < self.set_id {
			return Consider::RejectPast
		}
		if set_id > self.set_id {
			return Consider::RejectFuture
		}

		// only r-1 ... r+1
		if round.0 > self.round.0.saturating_add(1) {
			return Consider::RejectFuture
		}
		if round.0 < self.round.0.saturating_sub(1) {
			return Consider::RejectPast
		}

		Consider::Accept
	}

	/// Consider a set-id global message. Rounds are not taken into account, but are implicitly
	/// because we gate on finalization of a further block than a previous commit.
	fn consider_global(&self, set_id: SetId, number: N) -> Consider {
		// only from current set
		if set_id < self.set_id {
			return Consider::RejectPast
		}
		if set_id > self.set_id {
			return Consider::RejectFuture
		}

		// only commits which claim to prove a higher block number than
		// the one we're aware of.
		match self.last_commit {
			None => Consider::Accept,
			Some(ref num) =>
				if num < &number {
					Consider::Accept
				} else {
					Consider::RejectPast
				},
		}
	}
}

/// A local view of protocol state. Similar to `View` but we additionally track
/// the round and set id at which the last commit was observed, and the instant
/// at which the current round started.
struct LocalView<N> {
	round: Round,
	set_id: SetId,
	last_commit: Option<(N, Round, SetId)>,
	round_start: Instant,
}

impl<N> LocalView<N> {
	/// Creates a new `LocalView` at the given set id and round.
	fn new(set_id: SetId, round: Round) -> LocalView<N> {
		LocalView { set_id, round, last_commit: None, round_start: Instant::now() }
	}

	/// Converts the local view to a `View` discarding round and set id
	/// information about the last commit.
	fn as_view(&self) -> View<&N> {
		View { round: self.round, set_id: self.set_id, last_commit: self.last_commit_height() }
	}

	/// Update the set ID. implies a reset to round 1.
	fn update_set(&mut self, set_id: SetId) {
		if set_id != self.set_id {
			self.set_id = set_id;
			self.round = Round(1);
			self.round_start = Instant::now();
		}
	}

	/// Updates the current round.
	fn update_round(&mut self, round: Round) {
		self.round = round;
		self.round_start = Instant::now();
	}

	/// Returns the height of the block that the last observed commit finalizes.
	fn last_commit_height(&self) -> Option<&N> {
		self.last_commit.as_ref().map(|(number, _, _)| number)
	}
}

const KEEP_RECENT_ROUNDS: usize = 3;

/// Tracks gossip topics that we are keeping messages for. We keep topics of:
///
/// - the last `KEEP_RECENT_ROUNDS` complete GRANDPA rounds,
///
/// - the topic for the current and next round,
///
/// - and a global topic for commit and catch-up messages.
struct KeepTopics<B: BlockT> {
	current_set: SetId,
	rounds: VecDeque<(Round, SetId)>,
	reverse_map: AHashMap<B::Hash, (Option<Round>, SetId)>,
}

impl<B: BlockT> KeepTopics<B> {
	fn new() -> Self {
		KeepTopics {
			current_set: SetId(0),
			rounds: VecDeque::with_capacity(KEEP_RECENT_ROUNDS + 2),
			reverse_map: Default::default(),
		}
	}

	fn push(&mut self, round: Round, set_id: SetId) {
		self.current_set = std::cmp::max(self.current_set, set_id);

		// under normal operation the given round is already tracked (since we
		// track one round ahead). if we skip rounds (with a catch up) the given
		// round topic might not be tracked yet.
		if !self.rounds.contains(&(round, set_id)) {
			self.rounds.push_back((round, set_id));
		}

		// we also accept messages for the next round
		self.rounds.push_back((Round(round.0.saturating_add(1)), set_id));

		// the 2 is for the current and next round.
		while self.rounds.len() > KEEP_RECENT_ROUNDS + 2 {
			let _ = self.rounds.pop_front();
		}

		let mut map = AHashMap::with_capacity(KEEP_RECENT_ROUNDS + 3);
		map.insert(super::global_topic::<B>(self.current_set.0), (None, self.current_set));

		for &(round, set) in &self.rounds {
			map.insert(super::round_topic::<B>(round.0, set.0), (Some(round), set));
		}

		self.reverse_map = map;
	}

	fn topic_info(&self, topic: &B::Hash) -> Option<(Option<Round>, SetId)> {
		self.reverse_map.get(topic).cloned()
	}
}

// topics to send to a neighbor based on their view.
fn neighbor_topics<B: BlockT>(view: &View<NumberFor<B>>) -> Vec<B::Hash> {
	let s = view.set_id;
	let mut topics =
		vec![super::global_topic::<B>(s.0), super::round_topic::<B>(view.round.0, s.0)];

	if view.round.0 != 0 {
		let r = Round(view.round.0 - 1);
		topics.push(super::round_topic::<B>(r.0, s.0))
	}

	topics
}

/// Grandpa gossip message type.
/// This is the root type that gets encoded and sent on the network.
#[derive(Debug, Encode, Decode)]
pub(super) enum GossipMessage<Block: BlockT> {
	/// Grandpa message with round and set info.
	Vote(VoteMessage<Block>),
	/// Grandpa commit message with round and set info.
	Commit(FullCommitMessage<Block>),
	/// A neighbor packet. Not repropagated.
	Neighbor(VersionedNeighborPacket<NumberFor<Block>>),
	/// Grandpa catch up request message with round and set info. Not repropagated.
	CatchUpRequest(CatchUpRequestMessage),
	/// Grandpa catch up message with round and set info. Not repropagated.
	CatchUp(FullCatchUpMessage<Block>),
}

impl<Block: BlockT> From<NeighborPacket<NumberFor<Block>>> for GossipMessage<Block> {
	fn from(neighbor: NeighborPacket<NumberFor<Block>>) -> Self {
		GossipMessage::Neighbor(VersionedNeighborPacket::V1(neighbor))
	}
}

/// Network level vote message with topic information.
#[derive(Debug, Encode, Decode)]
pub(super) struct VoteMessage<Block: BlockT> {
	/// The round this message is from.
	pub(super) round: Round,
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
	/// The message itself.
	pub(super) message: SignedMessage<Block::Header>,
}

/// Network level commit message with topic information.
#[derive(Debug, Encode, Decode)]
pub(super) struct FullCommitMessage<Block: BlockT> {
	/// The round this message is from.
	pub(super) round: Round,
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
	/// The compact commit message.
	pub(super) message: CompactCommit<Block::Header>,
}

/// V1 neighbor packet. Neighbor packets are sent from nodes to their peers
/// and are not repropagated. These contain information about the node's state.
#[derive(Debug, Encode, Decode, Clone)]
pub(super) struct NeighborPacket<N> {
	/// The round the node is currently at.
	pub(super) round: Round,
	/// The set ID the node is currently at.
	pub(super) set_id: SetId,
	/// The highest finalizing commit observed.
	pub(super) commit_finalized_height: N,
}

/// A versioned neighbor packet.
#[derive(Debug, Encode, Decode)]
pub(super) enum VersionedNeighborPacket<N> {
	#[codec(index = 1)]
	V1(NeighborPacket<N>),
}

impl<N> VersionedNeighborPacket<N> {
	fn into_neighbor_packet(self) -> NeighborPacket<N> {
		match self {
			VersionedNeighborPacket::V1(p) => p,
		}
	}
}

/// A catch up request for a given round (or any further round) localized by set id.
#[derive(Clone, Debug, Encode, Decode)]
pub(super) struct CatchUpRequestMessage {
	/// The round that we want to catch up to.
	pub(super) round: Round,
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
}

/// Network level catch up message with topic information.
#[derive(Debug, Encode, Decode)]
pub(super) struct FullCatchUpMessage<Block: BlockT> {
	/// The voter set ID this message is from.
	pub(super) set_id: SetId,
	/// The compact commit message.
	pub(super) message: CatchUp<Block::Header>,
}

/// Misbehavior that peers can perform.
///
/// `cost` gives a cost that can be used to perform cost/benefit analysis of a
/// peer.
#[derive(Clone, Copy, Debug, PartialEq)]
pub(super) enum Misbehavior {
	// invalid neighbor message, considering the last one.
	InvalidViewChange,
	// could not decode neighbor message. bytes-length of the packet.
	UndecodablePacket(i32),
	// Bad catch up message (invalid signatures).
	BadCatchUpMessage { signatures_checked: i32 },
	// Bad commit message
	BadCommitMessage { signatures_checked: i32, blocks_loaded: i32, equivocations_caught: i32 },
	// A message received that's from the future relative to our view.
	// always misbehavior.
	FutureMessage,
	// A message received that cannot be evaluated relative to our view.
	// This happens before we have a view and have sent out neighbor packets.
	// always misbehavior.
	OutOfScopeMessage,
}

impl Misbehavior {
	pub(super) fn cost(&self) -> ReputationChange {
		use Misbehavior::*;

		match *self {
			InvalidViewChange => cost::INVALID_VIEW_CHANGE,
			UndecodablePacket(bytes) => ReputationChange::new(
				bytes.saturating_mul(cost::PER_UNDECODABLE_BYTE),
				"Grandpa: Bad packet",
			),
			BadCatchUpMessage { signatures_checked } => ReputationChange::new(
				cost::PER_SIGNATURE_CHECKED.saturating_mul(signatures_checked),
				"Grandpa: Bad cath-up message",
			),
			BadCommitMessage { signatures_checked, blocks_loaded, equivocations_caught } => {
				let cost = cost::PER_SIGNATURE_CHECKED
					.saturating_mul(signatures_checked)
					.saturating_add(cost::PER_BLOCK_LOADED.saturating_mul(blocks_loaded));

				let benefit = equivocations_caught.saturating_mul(benefit::PER_EQUIVOCATION);

				ReputationChange::new(
					(benefit as i32).saturating_add(cost as i32),
					"Grandpa: Bad commit",
				)
			},
			FutureMessage => cost::FUTURE_MESSAGE,
			OutOfScopeMessage => cost::OUT_OF_SCOPE_MESSAGE,
		}
	}
}

#[derive(Debug)]
struct PeerInfo<N> {
	view: View<N>,
	roles: ObservedRole,
}

impl<N> PeerInfo<N> {
	fn new(roles: ObservedRole) -> Self {
		PeerInfo { view: View::default(), roles }
	}
}

/// The peers we're connected to in gossip.
struct Peers<N> {
	inner: AHashMap<PeerId, PeerInfo<N>>,
	/// The randomly picked set of `LUCKY_PEERS` we'll gossip to in the first stage of round
	/// gossiping.
	first_stage_peers: AHashSet<PeerId>,
	/// The randomly picked set of peers we'll gossip to in the second stage of gossiping if the
	/// first stage didn't allow us to spread the voting data enough to conclude the round. This
	/// set should have size `sqrt(connected_peers)`.
	second_stage_peers: HashSet<PeerId>,
	/// The randomly picked set of `LUCKY_PEERS` light clients we'll gossip commit messages to.
	lucky_light_peers: HashSet<PeerId>,
}

impl<N> Default for Peers<N> {
	fn default() -> Self {
		Peers {
			inner: Default::default(),
			first_stage_peers: Default::default(),
			second_stage_peers: Default::default(),
			lucky_light_peers: Default::default(),
		}
	}
}

impl<N: Ord> Peers<N> {
	fn new_peer(&mut self, who: PeerId, role: ObservedRole) {
		match role {
			ObservedRole::Authority if self.first_stage_peers.len() < LUCKY_PEERS => {
				self.first_stage_peers.insert(who);
			},
			ObservedRole::Authority if self.second_stage_peers.len() < LUCKY_PEERS => {
				self.second_stage_peers.insert(who);
			},
			ObservedRole::Light if self.lucky_light_peers.len() < LUCKY_PEERS => {
				self.lucky_light_peers.insert(who);
			},
			_ => {},
		}

		self.inner.insert(who, PeerInfo::new(role));
	}

	fn peer_disconnected(&mut self, who: &PeerId) {
		self.inner.remove(who);
		// This does not happen often enough compared to round duration,
		// so we don't reshuffle.
		self.first_stage_peers.remove(who);
		self.second_stage_peers.remove(who);
		self.lucky_light_peers.remove(who);
	}

	// returns a reference to the new view, if the peer is known.
	fn update_peer_state(
		&mut self,
		who: &PeerId,
		update: NeighborPacket<N>,
	) -> Result<Option<&View<N>>, Misbehavior> {
		let peer = match self.inner.get_mut(who) {
			None => return Ok(None),
			Some(p) => p,
		};

		let invalid_change = peer.view.set_id > update.set_id ||
			peer.view.round > update.round && peer.view.set_id == update.set_id ||
			peer.view.last_commit.as_ref() > Some(&update.commit_finalized_height);

		if invalid_change {
			return Err(Misbehavior::InvalidViewChange)
		}

		peer.view = View {
			round: update.round,
			set_id: update.set_id,
			last_commit: Some(update.commit_finalized_height),
		};

		trace!(target: "afg", "Peer {} updated view. Now at {:?}, {:?}",
			who, peer.view.round, peer.view.set_id);

		Ok(Some(&peer.view))
	}

	fn update_commit_height(&mut self, who: &PeerId, new_height: N) -> Result<(), Misbehavior> {
		let peer = match self.inner.get_mut(who) {
			None => return Ok(()),
			Some(p) => p,
		};

		// this doesn't allow a peer to send us unlimited commits with the
		// same height, because there is still a misbehavior condition based on
		// sending commits that are <= the best we are aware of.
		if peer.view.last_commit.as_ref() > Some(&new_height) {
			return Err(Misbehavior::InvalidViewChange)
		}

		peer.view.last_commit = Some(new_height);

		Ok(())
	}

	fn peer<'a>(&'a self, who: &PeerId) -> Option<&'a PeerInfo<N>> {
		self.inner.get(who)
	}

	fn reshuffle(&mut self) {
		// we want to randomly select peers into three sets according to the following logic:
		// - first set: LUCKY_PEERS random peers where at least LUCKY_PEERS/2 are authorities
		//   (unless
		// we're not connected to that many authorities)
		// - second set: max(LUCKY_PEERS, sqrt(peers)) peers where at least LUCKY_PEERS are
		//   authorities.
		// - third set: LUCKY_PEERS random light client peers

		let shuffled_peers = {
			let mut peers =
				self.inner.iter().map(|(peer_id, info)| (*peer_id, info)).collect::<Vec<_>>();

			peers.shuffle(&mut rand::thread_rng());
			peers
		};

		let shuffled_authorities = shuffled_peers.iter().filter_map(|(peer_id, info)| {
			if matches!(info.roles, ObservedRole::Authority) {
				Some(peer_id)
			} else {
				None
			}
		});

		let mut first_stage_peers = AHashSet::new();
		let mut second_stage_peers = HashSet::new();

		// we start by allocating authorities to the first stage set and when the minimum of
		// `LUCKY_PEERS / 2` is filled we start allocating to the second stage set.
		let half_lucky = LUCKY_PEERS / 2;
		let one_and_a_half_lucky = LUCKY_PEERS + half_lucky;
		for (n_authorities_added, peer_id) in shuffled_authorities.enumerate() {
			if n_authorities_added < half_lucky {
				first_stage_peers.insert(*peer_id);
			} else if n_authorities_added < one_and_a_half_lucky {
				second_stage_peers.insert(*peer_id);
			} else {
				break
			}
		}

		// fill up first and second sets with remaining peers (either full or authorities)
		// prioritizing filling the first set over the second.
		let n_second_stage_peers = LUCKY_PEERS.max((shuffled_peers.len() as f32).sqrt() as usize);
		for (peer_id, info) in &shuffled_peers {
			if info.roles.is_light() {
				continue
			}

			if first_stage_peers.len() < LUCKY_PEERS {
				first_stage_peers.insert(*peer_id);
				second_stage_peers.remove(peer_id);
			} else if second_stage_peers.len() < n_second_stage_peers {
				if !first_stage_peers.contains(peer_id) {
					second_stage_peers.insert(*peer_id);
				}
			} else {
				break
			}
		}

		// pick `LUCKY_PEERS` random light peers
		let lucky_light_peers = shuffled_peers
			.into_iter()
			.filter_map(|(peer_id, info)| if info.roles.is_light() { Some(peer_id) } else { None })
			.take(LUCKY_PEERS)
			.collect();

		self.first_stage_peers = first_stage_peers;
		self.second_stage_peers = second_stage_peers;
		self.lucky_light_peers = lucky_light_peers;
	}
}

#[derive(Debug, PartialEq)]
pub(super) enum Action<H> {
	// repropagate under given topic, to the given peers, applying cost/benefit to originator.
	Keep(H, ReputationChange),
	// discard and process.
	ProcessAndDiscard(H, ReputationChange),
	// discard, applying cost/benefit to originator.
	Discard(ReputationChange),
}

/// State of catch up request handling.
#[derive(Debug)]
enum PendingCatchUp {
	/// No pending catch up requests.
	None,
	/// Pending catch up request which has not been answered yet.
	Requesting { who: PeerId, request: CatchUpRequestMessage, instant: Instant },
	/// Pending catch up request that was answered and is being processed.
	Processing { instant: Instant },
}

/// Configuration for the round catch-up mechanism.
enum CatchUpConfig {
	/// Catch requests are enabled, our node will issue them whenever it sees a
	/// neighbor packet for a round further than `CATCH_UP_THRESHOLD`. If
	/// `only_from_authorities` is set, the node will only send catch-up
	/// requests to other authorities it is connected to. This is useful if the
	/// GRANDPA observer protocol is live on the network, in which case full
	/// nodes (non-authorities) don't have the necessary round data to answer
	/// catch-up requests.
	Enabled { only_from_authorities: bool },
	/// Catch-up requests are disabled, our node will never issue them. This is
	/// useful for the GRANDPA observer mode, where we are only interested in
	/// commit messages and don't need to follow the full round protocol.
	Disabled,
}

impl CatchUpConfig {
	fn enabled(only_from_authorities: bool) -> CatchUpConfig {
		CatchUpConfig::Enabled { only_from_authorities }
	}

	fn disabled() -> CatchUpConfig {
		CatchUpConfig::Disabled
	}

	fn request_allowed<N>(&self, peer: &PeerInfo<N>) -> bool {
		match self {
			CatchUpConfig::Disabled => false,
			CatchUpConfig::Enabled { only_from_authorities, .. } => match peer.roles {
				ObservedRole::Authority => true,
				ObservedRole::Light => false,
				ObservedRole::Full => !only_from_authorities,
			},
		}
	}
}

struct Inner<Block: BlockT> {
	local_view: Option<LocalView<NumberFor<Block>>>,
	peers: Peers<NumberFor<Block>>,
	live_topics: KeepTopics<Block>,
	authorities: Vec<AuthorityId>,
	config: crate::Config,
	next_rebroadcast: Instant,
	pending_catch_up: PendingCatchUp,
	catch_up_config: CatchUpConfig,
}

type MaybeMessage<Block> = Option<(Vec<PeerId>, NeighborPacket<NumberFor<Block>>)>;

impl<Block: BlockT> Inner<Block> {
	fn new(config: crate::Config) -> Self {
		let catch_up_config = if config.observer_enabled {
			if config.local_role.is_authority() {
				// since the observer protocol is enabled, we will only issue
				// catch-up requests if we are an authority (and only to other
				// authorities).
				CatchUpConfig::enabled(true)
			} else {
				// otherwise, we are running the observer protocol and don't
				// care about catch-up requests.
				CatchUpConfig::disabled()
			}
		} else {
			// if the observer protocol isn't enabled and we're not a light client, then any full
			// node should be able to answer catch-up requests.
			CatchUpConfig::enabled(false)
		};

		Inner {
			local_view: None,
			peers: Peers::default(),
			live_topics: KeepTopics::new(),
			next_rebroadcast: Instant::now() + REBROADCAST_AFTER,
			authorities: Vec::new(),
			pending_catch_up: PendingCatchUp::None,
			catch_up_config,
			config,
		}
	}

	/// Note a round in the current set has started.
	fn note_round(&mut self, round: Round) -> MaybeMessage<Block> {
		{
			let local_view = match self.local_view {
				None => return None,
				Some(ref mut v) =>
					if v.round == round {
						return None
					} else {
						v
					},
			};

			let set_id = local_view.set_id;

			debug!(target: "afg", "Voter {} noting beginning of round {:?} to network.",
				self.config.name(), (round, set_id));

			local_view.update_round(round);

			self.live_topics.push(round, set_id);
			self.peers.reshuffle();
		}
		self.multicast_neighbor_packet()
	}

	/// Note that a voter set with given ID has started. Does nothing if the last
	/// call to the function was with the same `set_id`.
	fn note_set(&mut self, set_id: SetId, authorities: Vec<AuthorityId>) -> MaybeMessage<Block> {
		{
			let local_view = match self.local_view {
				ref mut x @ None => x.get_or_insert(LocalView::new(set_id, Round(1))),
				Some(ref mut v) =>
					if v.set_id == set_id {
						let diff_authorities = self.authorities.iter().collect::<HashSet<_>>() !=
							authorities.iter().collect::<HashSet<_>>();

						if diff_authorities {
							debug!(target: "afg",
								"Gossip validator noted set {:?} twice with different authorities. \
								Was the authority set hard forked?",
								set_id,
							);
							self.authorities = authorities;
						}
						return None
					} else {
						v
					},
			};

			local_view.update_set(set_id);
			self.live_topics.push(Round(1), set_id);
			self.authorities = authorities;
		}
		self.multicast_neighbor_packet()
	}

	/// Note that we've imported a commit finalizing a given block.
	fn note_commit_finalized(
		&mut self,
		round: Round,
		set_id: SetId,
		finalized: NumberFor<Block>,
	) -> MaybeMessage<Block> {
		{
			match self.local_view {
				None => return None,
				Some(ref mut v) =>
					if v.last_commit_height() < Some(&finalized) {
						v.last_commit = Some((finalized, round, set_id));
					} else {
						return None
					},
			};
		}

		self.multicast_neighbor_packet()
	}

	fn consider_vote(&self, round: Round, set_id: SetId) -> Consider {
		self.local_view
			.as_ref()
			.map(LocalView::as_view)
			.map(|v| v.consider_vote(round, set_id))
			.unwrap_or(Consider::RejectOutOfScope)
	}

	fn consider_global(&self, set_id: SetId, number: NumberFor<Block>) -> Consider {
		self.local_view
			.as_ref()
			.map(LocalView::as_view)
			.map(|v| v.consider_global(set_id, &number))
			.unwrap_or(Consider::RejectOutOfScope)
	}

	fn cost_past_rejection(
		&self,
		_who: &PeerId,
		_round: Round,
		_set_id: SetId,
	) -> ReputationChange {
		// hardcoded for now.
		cost::PAST_REJECTION
	}

	fn validate_round_message(
		&self,
		who: &PeerId,
		full: &VoteMessage<Block>,
	) -> Action<Block::Hash> {
		match self.consider_vote(full.round, full.set_id) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectOutOfScope =>
				return Action::Discard(Misbehavior::OutOfScopeMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::Accept => {},
		}

		// ensure authority is part of the set.
		if !self.authorities.contains(&full.message.id) {
			debug!(target: "afg", "Message from unknown voter: {}", full.message.id);
			telemetry!(
				self.config.telemetry;
				CONSENSUS_DEBUG;
				"afg.bad_msg_signature";
				"signature" => ?full.message.id,
			);
			return Action::Discard(cost::UNKNOWN_VOTER)
		}

		if !sp_finality_grandpa::check_message_signature(
			&full.message.message,
			&full.message.id,
			&full.message.signature,
			full.round.0,
			full.set_id.0,
		) {
			debug!(target: "afg", "Bad message signature {}", full.message.id);
			telemetry!(
				self.config.telemetry;
				CONSENSUS_DEBUG;
				"afg.bad_msg_signature";
				"signature" => ?full.message.id,
			);
			return Action::Discard(cost::BAD_SIGNATURE)
		}

		let topic = super::round_topic::<Block>(full.round.0, full.set_id.0);
		Action::Keep(topic, benefit::ROUND_MESSAGE)
	}

	fn validate_commit_message(
		&mut self,
		who: &PeerId,
		full: &FullCommitMessage<Block>,
	) -> Action<Block::Hash> {
		if let Err(misbehavior) = self.peers.update_commit_height(who, full.message.target_number) {
			return Action::Discard(misbehavior.cost())
		}

		match self.consider_global(full.set_id, full.message.target_number) {
			Consider::RejectFuture => return Action::Discard(Misbehavior::FutureMessage.cost()),
			Consider::RejectPast =>
				return Action::Discard(self.cost_past_rejection(who, full.round, full.set_id)),
			Consider::RejectOutOfScope =>
				return Action::Discard(Misbehavior::OutOfScopeMessage.cost()),
			Consider::Accept => {},
		}

		if full.message.precommits.len() != full.message.auth_data.len() ||
			full.message.precommits.is_empty()
		{
			debug!(target: "afg", "Malformed compact commit");
			telemetry!(
				self.config.telemetry;
				CONSENSUS_DEBUG;
				"afg.malformed_compact_commit";
				"precommits_len" => ?full.message.precommits.len(),
				"auth_data_len" => ?full.message.auth_data.len(),
				"precommits_is_empty" => ?full.message.precommits.is_empty(),
			);
			return Action::Discard(cost::MALFORMED_COMMIT)
		}

		// always discard commits initially and rebroadcast after doing full
		// checking.
		let topic = super::global_topic::<Block>(full.set_id.0);
		Action::ProcessAndDiscard(topic, benefit::BASIC_VALIDATED_COMMIT)
	}

	fn validate_catch_up_message(
		&mut self,
		who: &PeerId,
		full: &FullCatchUpMessage<Block>,
	) -> Action<Block::Hash> {
		match &self.pending_catch_up {
			PendingCatchUp::Requesting { who: peer, request, instant } => {
				if peer != who {
					return Action::Discard(Misbehavior::OutOfScopeMessage.cost())
				}

				if request.set_id != full.set_id {
					return Action::Discard(cost::MALFORMED_CATCH_UP)
				}

				if request.round.0 > full.message.round_number {
					return Action::Discard(cost::MALFORMED_CATCH_UP)
				}

				if full.message.prevotes.is_empty() || full.message.precommits.is_empty() {
					return Action::Discard(cost::MALFORMED_CATCH_UP)
				}

				// move request to pending processing state, we won't push out
				// any catch up requests until we import this one (either with a
				// success or failure).
				self.pending_catch_up = PendingCatchUp::Processing { instant: *instant };

				// always discard catch up messages, they're point-to-point
				let topic = super::global_topic::<Block>(full.set_id.0);
				Action::ProcessAndDiscard(topic, benefit::BASIC_VALIDATED_CATCH_UP)
			},
			_ => Action::Discard(Misbehavior::OutOfScopeMessage.cost()),
		}
	}

	fn note_catch_up_message_processed(&mut self) {
		match &self.pending_catch_up {
			PendingCatchUp::Processing { .. } => {
				self.pending_catch_up = PendingCatchUp::None;
			},
			state => debug!(target: "afg",
				"Noted processed catch up message when state was: {:?}",
				state,
			),
		}
	}

	fn handle_catch_up_request(
		&mut self,
		who: &PeerId,
		request: CatchUpRequestMessage,
		set_state: &environment::SharedVoterSetState<Block>,
	) -> (Option<GossipMessage<Block>>, Action<Block::Hash>) {
		let local_view = match self.local_view {
			None => return (None, Action::Discard(Misbehavior::OutOfScopeMessage.cost())),
			Some(ref view) => view,
		};

		if request.set_id != local_view.set_id {
			// NOTE: When we're close to a set change there is potentially a
			// race where the peer sent us the request before it observed that
			// we had transitioned to a new set. In this case we charge a lower
			// cost.
			if request.set_id.0.saturating_add(1) == local_view.set_id.0 &&
				local_view.round.0.saturating_sub(CATCH_UP_THRESHOLD) == 0
			{
				return (None, Action::Discard(cost::HONEST_OUT_OF_SCOPE_CATCH_UP))
			}

			return (None, Action::Discard(Misbehavior::OutOfScopeMessage.cost()))
		}

		match self.peers.peer(who) {
			None => return (None, Action::Discard(Misbehavior::OutOfScopeMessage.cost())),
			Some(peer) if peer.view.round >= request.round =>
				return (None, Action::Discard(Misbehavior::OutOfScopeMessage.cost())),
			_ => {},
		}

		let last_completed_round = set_state.read().last_completed_round();
		if last_completed_round.number < request.round.0 {
			return (None, Action::Discard(Misbehavior::OutOfScopeMessage.cost()))
		}

		trace!(target: "afg", "Replying to catch-up request for round {} from {} with round {}",
			request.round.0,
			who,
			last_completed_round.number,
		);

		let mut prevotes = Vec::new();
		let mut precommits = Vec::new();

		// NOTE: the set of votes stored in `LastCompletedRound` is a minimal
		// set of votes, i.e. at most one equivocation is stored per voter. The
		// code below assumes this invariant is maintained when creating the
		// catch up reply since peers won't accept catch-up messages that have
		// too many equivocations (we exceed the fault-tolerance bound).
		for vote in last_completed_round.votes {
			match vote.message {
				finality_grandpa::Message::Prevote(prevote) => {
					prevotes.push(finality_grandpa::SignedPrevote {
						prevote,
						signature: vote.signature,
						id: vote.id,
					});
				},
				finality_grandpa::Message::Precommit(precommit) => {
					precommits.push(finality_grandpa::SignedPrecommit {
						precommit,
						signature: vote.signature,
						id: vote.id,
					});
				},
				_ => {},
			}
		}

		let (base_hash, base_number) = last_completed_round.base;

		let catch_up = CatchUp::<Block::Header> {
			round_number: last_completed_round.number,
			prevotes,
			precommits,
			base_hash,
			base_number,
		};

		let full_catch_up = GossipMessage::CatchUp::<Block>(FullCatchUpMessage {
			set_id: request.set_id,
			message: catch_up,
		});

		(Some(full_catch_up), Action::Discard(cost::CATCH_UP_REPLY))
	}

	fn try_catch_up(&mut self, who: &PeerId) -> (Option<GossipMessage<Block>>, Option<Report>) {
		let mut catch_up = None;
		let mut report = None;

		// if the peer is on the same set and ahead of us by a margin bigger
		// than `CATCH_UP_THRESHOLD` then we should ask it for a catch up
		// message. we only send catch-up requests to authorities, observers
		// won't be able to reply since they don't follow the full GRANDPA
		// protocol and therefore might not have the vote data available.
		if let (Some(peer), Some(local_view)) = (self.peers.peer(who), &self.local_view) {
			if self.catch_up_config.request_allowed(peer) &&
				peer.view.set_id == local_view.set_id &&
				peer.view.round.0.saturating_sub(CATCH_UP_THRESHOLD) > local_view.round.0
			{
				// send catch up request if allowed
				let round = peer.view.round.0 - 1; // peer.view.round is > 0
				let request =
					CatchUpRequestMessage { set_id: peer.view.set_id, round: Round(round) };

				let (catch_up_allowed, catch_up_report) = self.note_catch_up_request(who, &request);

				if catch_up_allowed {
					debug!(target: "afg", "Sending catch-up request for round {} to {}",
						   round,
						   who,
					);

					catch_up = Some(GossipMessage::<Block>::CatchUpRequest(request));
				}

				report = catch_up_report;
			}
		}

		(catch_up, report)
	}

	fn import_neighbor_message(
		&mut self,
		who: &PeerId,
		update: NeighborPacket<NumberFor<Block>>,
	) -> (Vec<Block::Hash>, Action<Block::Hash>, Option<GossipMessage<Block>>, Option<Report>) {
		let update_res = self.peers.update_peer_state(who, update);

		let (cost_benefit, topics) = match update_res {
			Ok(view) =>
				(benefit::NEIGHBOR_MESSAGE, view.map(|view| neighbor_topics::<Block>(view))),
			Err(misbehavior) => (misbehavior.cost(), None),
		};

		let (catch_up, report) = match update_res {
			Ok(_) => self.try_catch_up(who),
			_ => (None, None),
		};

		let neighbor_topics = topics.unwrap_or_default();

		// always discard neighbor messages, it's only valid for one hop.
		let action = Action::Discard(cost_benefit);

		(neighbor_topics, action, catch_up, report)
	}

	fn multicast_neighbor_packet(&self) -> MaybeMessage<Block> {
		self.local_view.as_ref().map(|local_view| {
			let packet = NeighborPacket {
				round: local_view.round,
				set_id: local_view.set_id,
				commit_finalized_height: *local_view.last_commit_height().unwrap_or(&Zero::zero()),
			};

			let peers = self
				.peers
				.inner
				.iter()
				.filter_map(|(id, info)| {
					// light clients don't participate in the full GRANDPA voter protocol
					// and therefore don't need to be informed about view updates
					if info.roles.is_light() {
						None
					} else {
						Some(id)
					}
				})
				.cloned()
				.collect();

			(peers, packet)
		})
	}

	fn note_catch_up_request(
		&mut self,
		who: &PeerId,
		catch_up_request: &CatchUpRequestMessage,
	) -> (bool, Option<Report>) {
		let report = match &self.pending_catch_up {
			PendingCatchUp::Requesting { who: peer, instant, .. } => {
				if instant.elapsed() <= CATCH_UP_REQUEST_TIMEOUT {
					return (false, None)
				} else {
					// report peer for timeout
					Some((*peer, cost::CATCH_UP_REQUEST_TIMEOUT))
				}
			},
			PendingCatchUp::Processing { instant, .. } => {
				if instant.elapsed() < CATCH_UP_PROCESS_TIMEOUT {
					return (false, None)
				} else {
					None
				}
			},
			_ => None,
		};

		self.pending_catch_up = PendingCatchUp::Requesting {
			who: *who,
			request: catch_up_request.clone(),
			instant: Instant::now(),
		};

		(true, report)
	}

	/// The initial logic for filtering round messages follows the given state
	/// transitions:
	///
	/// - State 1: allowed to LUCKY_PEERS random peers (where at least LUCKY_PEERS/2 are
	///   authorities)
	/// - State 2: allowed to max(LUCKY_PEERS, sqrt(random peers)) (where at least LUCKY_PEERS are
	///   authorities)
	/// - State 3: allowed to all peers
	///
	/// Transitions will be triggered on repropagation attempts by the underlying gossip layer.
	fn round_message_allowed(&self, who: &PeerId) -> bool {
		let round_duration = self.config.gossip_duration * ROUND_DURATION;
		let round_elapsed = match self.local_view {
			Some(ref local_view) => local_view.round_start.elapsed(),
			None => return false,
		};

		if round_elapsed < round_duration.mul_f32(PROPAGATION_SOME) {
			self.peers.first_stage_peers.contains(who)
		} else if round_elapsed < round_duration.mul_f32(PROPAGATION_ALL) {
			self.peers.first_stage_peers.contains(who) ||
				self.peers.second_stage_peers.contains(who)
		} else {
			self.peers.peer(who).map(|info| !info.roles.is_light()).unwrap_or(false)
		}
	}

	/// The initial logic for filtering global messages follows the given state
	/// transitions:
	///
	/// - State 1: allowed to max(LUCKY_PEERS, sqrt(peers)) (where at least LUCKY_PEERS are
	///   authorities)
	/// - State 2: allowed to all peers
	///
	/// We are more lenient with global messages since there should be a lot
	/// less global messages than round messages (just commits), and we want
	/// these to propagate to non-authorities fast enough so that they can
	/// observe finality.
	///
	/// Transitions will be triggered on repropagation attempts by the
	/// underlying gossip layer, which should happen every 30 seconds.
	fn global_message_allowed(&self, who: &PeerId) -> bool {
		let round_duration = self.config.gossip_duration * ROUND_DURATION;
		let round_elapsed = match self.local_view {
			Some(ref local_view) => local_view.round_start.elapsed(),
			None => return false,
		};

		if round_elapsed < round_duration.mul_f32(PROPAGATION_ALL) {
			self.peers.first_stage_peers.contains(who) ||
				self.peers.second_stage_peers.contains(who) ||
				self.peers.lucky_light_peers.contains(who)
		} else {
			true
		}
	}
}

// Prometheus metrics for [`GossipValidator`].
pub(crate) struct Metrics {
	messages_validated: CounterVec<U64>,
}

impl Metrics {
	pub(crate) fn register(
		registry: &prometheus_endpoint::Registry,
	) -> Result<Self, PrometheusError> {
		Ok(Self {
			messages_validated: register(
				CounterVec::new(
					Opts::new(
						"substrate_finality_grandpa_communication_gossip_validator_messages",
						"Number of messages validated by the finality grandpa gossip validator.",
					),
					&["message", "action"],
				)?,
				registry,
			)?,
		})
	}
}

/// A validator for GRANDPA gossip messages.
pub(super) struct GossipValidator<Block: BlockT> {
	inner: parking_lot::RwLock<Inner<Block>>,
	set_state: environment::SharedVoterSetState<Block>,
	report_sender: TracingUnboundedSender<PeerReport>,
	metrics: Option<Metrics>,
	telemetry: Option<TelemetryHandle>,
}

impl<Block: BlockT> GossipValidator<Block> {
	/// Create a new gossip-validator. The current set is initialized to 0. If
	/// `catch_up_enabled` is set to false then the validator will not issue any
	/// catch up requests (useful e.g. when running just the GRANDPA observer).
	pub(super) fn new(
		config: crate::Config,
		set_state: environment::SharedVoterSetState<Block>,
		prometheus_registry: Option<&Registry>,
		telemetry: Option<TelemetryHandle>,
	) -> (GossipValidator<Block>, TracingUnboundedReceiver<PeerReport>) {
		let metrics = match prometheus_registry.map(Metrics::register) {
			Some(Ok(metrics)) => Some(metrics),
			Some(Err(e)) => {
				debug!(target: "afg", "Failed to register metrics: {:?}", e);
				None
			},
			None => None,
		};

		let (tx, rx) = tracing_unbounded("mpsc_grandpa_gossip_validator");
		let val = GossipValidator {
			inner: parking_lot::RwLock::new(Inner::new(config)),
			set_state,
			report_sender: tx,
			metrics,
			telemetry,
		};

		(val, rx)
	}

	/// Note a round in the current set has started.
	pub(super) fn note_round<F>(&self, round: Round, send_neighbor: F)
	where
		F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>),
	{
		let maybe_msg = self.inner.write().note_round(round);
		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	/// Note that a voter set with given ID has started. Updates the current set to given
	/// value and initializes the round to 0.
	pub(super) fn note_set<F>(&self, set_id: SetId, authorities: Vec<AuthorityId>, send_neighbor: F)
	where
		F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>),
	{
		let maybe_msg = self.inner.write().note_set(set_id, authorities);
		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	/// Note that we've imported a commit finalizing a given block.
	pub(super) fn note_commit_finalized<F>(
		&self,
		round: Round,
		set_id: SetId,
		finalized: NumberFor<Block>,
		send_neighbor: F,
	) where
		F: FnOnce(Vec<PeerId>, NeighborPacket<NumberFor<Block>>),
	{
		let maybe_msg = self.inner.write().note_commit_finalized(round, set_id, finalized);

		if let Some((to, msg)) = maybe_msg {
			send_neighbor(to, msg);
		}
	}

	/// Note that we've processed a catch up message.
	pub(super) fn note_catch_up_message_processed(&self) {
		self.inner.write().note_catch_up_message_processed();
	}

	fn report(&self, who: PeerId, cost_benefit: ReputationChange) {
		let _ = self.report_sender.unbounded_send(PeerReport { who, cost_benefit });
	}

	pub(super) fn do_validate(
		&self,
		who: &PeerId,
		mut data: &[u8],
	) -> (Action<Block::Hash>, Vec<Block::Hash>, Option<GossipMessage<Block>>) {
		let mut broadcast_topics = Vec::new();
		let mut peer_reply = None;

		// Message name for Prometheus metric recording.
		let message_name;

		let action = {
			match GossipMessage::<Block>::decode(&mut data) {
				Ok(GossipMessage::Vote(ref message)) => {
					message_name = Some("vote");
					self.inner.write().validate_round_message(who, message)
				},
				Ok(GossipMessage::Commit(ref message)) => {
					message_name = Some("commit");
					self.inner.write().validate_commit_message(who, message)
				},
				Ok(GossipMessage::Neighbor(update)) => {
					message_name = Some("neighbor");
					let (topics, action, catch_up, report) = self
						.inner
						.write()
						.import_neighbor_message(who, update.into_neighbor_packet());

					if let Some((peer, cost_benefit)) = report {
						self.report(peer, cost_benefit);
					}

					broadcast_topics = topics;
					peer_reply = catch_up;
					action
				},
				Ok(GossipMessage::CatchUp(ref message)) => {
					message_name = Some("catch_up");
					self.inner.write().validate_catch_up_message(who, message)
				},
				Ok(GossipMessage::CatchUpRequest(request)) => {
					message_name = Some("catch_up_request");
					let (reply, action) =
						self.inner.write().handle_catch_up_request(who, request, &self.set_state);

					peer_reply = reply;
					action
				},
				Err(e) => {
					message_name = None;
					debug!(target: "afg", "Error decoding message: {}", e);
					telemetry!(
						self.telemetry;
						CONSENSUS_DEBUG;
						"afg.err_decoding_msg";
						"" => "",
					);

					let len = std::cmp::min(i32::MAX as usize, data.len()) as i32;
					Action::Discard(Misbehavior::UndecodablePacket(len).cost())
				},
			}
		};

		// Prometheus metric recording.
		if let (Some(metrics), Some(message_name)) = (&self.metrics, message_name) {
			let action_name = match action {
				Action::Keep(_, _) => "keep",
				Action::ProcessAndDiscard(_, _) => "process_and_discard",
				Action::Discard(_) => "discard",
			};
			metrics.messages_validated.with_label_values(&[message_name, action_name]).inc();
		}

		(action, broadcast_topics, peer_reply)
	}

	#[cfg(test)]
	fn inner(&self) -> &parking_lot::RwLock<Inner<Block>> {
		&self.inner
	}
}

impl<Block: BlockT> sc_network_gossip::Validator<Block> for GossipValidator<Block> {
	fn new_peer(
		&self,
		context: &mut dyn ValidatorContext<Block>,
		who: &PeerId,
		roles: ObservedRole,
	) {
		let packet = {
			let mut inner = self.inner.write();
			inner.peers.new_peer(*who, roles);

			inner.local_view.as_ref().map(|v| NeighborPacket {
				round: v.round,
				set_id: v.set_id,
				commit_finalized_height: *v.last_commit_height().unwrap_or(&Zero::zero()),
			})
		};

		if let Some(packet) = packet {
			let packet_data = GossipMessage::<Block>::from(packet).encode();
			context.send_message(who, packet_data);
		}
	}

	fn peer_disconnected(&self, _context: &mut dyn ValidatorContext<Block>, who: &PeerId) {
		self.inner.write().peers.peer_disconnected(who);
	}

	fn validate(
		&self,
		context: &mut dyn ValidatorContext<Block>,
		who: &PeerId,
		data: &[u8],
	) -> sc_network_gossip::ValidationResult<Block::Hash> {
		let (action, broadcast_topics, peer_reply) = self.do_validate(who, data);

		// not with lock held!
		if let Some(msg) = peer_reply {
			context.send_message(who, msg.encode());
		}

		for topic in broadcast_topics {
			context.send_topic(who, topic, false);
		}

		match action {
			Action::Keep(topic, cb) => {
				self.report(*who, cb);
				context.broadcast_message(topic, data.to_vec(), false);
				sc_network_gossip::ValidationResult::ProcessAndKeep(topic)
			},
			Action::ProcessAndDiscard(topic, cb) => {
				self.report(*who, cb);
				sc_network_gossip::ValidationResult::ProcessAndDiscard(topic)
			},
			Action::Discard(cb) => {
				self.report(*who, cb);
				sc_network_gossip::ValidationResult::Discard
			},
		}
	}

	fn message_allowed<'a>(
		&'a self,
	) -> Box<dyn FnMut(&PeerId, MessageIntent, &Block::Hash, &[u8]) -> bool + 'a> {
		let (inner, do_rebroadcast) = {
			use parking_lot::RwLockWriteGuard;

			let mut inner = self.inner.write();
			let now = Instant::now();
			let do_rebroadcast = if now >= inner.next_rebroadcast {
				inner.next_rebroadcast = now + REBROADCAST_AFTER;
				true
			} else {
				false
			};

			// downgrade to read-lock.
			(RwLockWriteGuard::downgrade(inner), do_rebroadcast)
		};

		Box::new(move |who, intent, topic, mut data| {
			if let MessageIntent::PeriodicRebroadcast = intent {
				return do_rebroadcast
			}

			let peer = match inner.peers.peer(who) {
				None => return false,
				Some(x) => x,
			};

			// if the topic is not something we're keeping at the moment,
			// do not send.
			let (maybe_round, set_id) = match inner.live_topics.topic_info(topic) {
				None => return false,
				Some(x) => x,
			};

			if let MessageIntent::Broadcast = intent {
				if maybe_round.is_some() {
					if !inner.round_message_allowed(who) {
						// early return if the vote message isn't allowed at this stage.
						return false
					}
				} else if !inner.global_message_allowed(who) {
					// early return if the global message isn't allowed at this stage.
					return false
				}
			}

			// if the topic is not something the peer accepts, discard.
			if let Some(round) = maybe_round {
				return peer.view.consider_vote(round, set_id) == Consider::Accept
			}

			// global message.
			let local_view = match inner.local_view {
				Some(ref v) => v,
				None => return false, // cannot evaluate until we have a local view.
			};

			match GossipMessage::<Block>::decode(&mut data) {
				Err(_) => false,
				Ok(GossipMessage::Commit(full)) => {
					// we only broadcast commit messages if they're for the same
					// set the peer is in and if the commit is better than the
					// last received by peer, additionally we make sure to only
					// broadcast our best commit.
					peer.view.consider_global(set_id, full.message.target_number) ==
						Consider::Accept && Some(&full.message.target_number) ==
						local_view.last_commit_height()
				},
				Ok(GossipMessage::Neighbor(_)) => false,
				Ok(GossipMessage::CatchUpRequest(_)) => false,
				Ok(GossipMessage::CatchUp(_)) => false,
				Ok(GossipMessage::Vote(_)) => false, // should not be the case.
			}
		})
	}

	fn message_expired<'a>(&'a self) -> Box<dyn FnMut(Block::Hash, &[u8]) -> bool + 'a> {
		let inner = self.inner.read();
		Box::new(move |topic, mut data| {
			// if the topic is not one of the ones that we are keeping at the moment,
			// it is expired.
			match inner.live_topics.topic_info(&topic) {
				None => return true,
				// round messages don't require further checking.
				Some((Some(_), _)) => return false,
				Some((None, _)) => {},
			};

			let local_view = match inner.local_view {
				Some(ref v) => v,
				None => return true, // no local view means we can't evaluate or hold any topic.
			};

			// global messages -- only keep the best commit.
			match GossipMessage::<Block>::decode(&mut data) {
				Err(_) => true,
				Ok(GossipMessage::Commit(full)) => match local_view.last_commit {
					Some((number, round, set_id)) =>
					// we expire any commit message that doesn't target the same block
					// as our best commit or isn't from the same round and set id
						!(full.message.target_number == number &&
							full.round == round && full.set_id == set_id),
					None => true,
				},
				Ok(_) => true,
			}
		})
	}
}

/// Report specifying a reputation change for a given peer.
pub(super) struct PeerReport {
	pub who: PeerId,
	pub cost_benefit: ReputationChange,
}

#[cfg(test)]
mod tests {
	use super::{environment::SharedVoterSetState, *};
	use crate::communication;
	use sc_network::config::Role;
	use sc_network_gossip::Validator as GossipValidatorT;
	use sp_core::{crypto::UncheckedFrom, H256};
	use substrate_test_runtime_client::runtime::{Block, Header};

	// some random config (not really needed)
	fn config() -> crate::Config {
		crate::Config {
			gossip_duration: Duration::from_millis(10),
			justification_period: 256,
			keystore: None,
			name: None,
			local_role: Role::Authority,
			observer_enabled: true,
			telemetry: None,
			protocol_name: communication::grandpa_protocol_name::NAME.into(),
		}
	}

	// dummy voter set state
	fn voter_set_state() -> SharedVoterSetState<Block> {
		use crate::{authorities::AuthoritySet, environment::VoterSetState};

		let base = (H256::zero(), 0);

		let voters = vec![(AuthorityId::unchecked_from([1; 32]), 1)];
		let voters = AuthoritySet::genesis(voters).unwrap();

		let set_state = VoterSetState::live(0, &voters, base);

		set_state.into()
	}

	#[test]
	fn view_vote_rules() {
		let view = View { round: Round(100), set_id: SetId(1), last_commit: Some(1000u64) };

		assert_eq!(view.consider_vote(Round(98), SetId(1)), Consider::RejectPast);
		assert_eq!(view.consider_vote(Round(1), SetId(0)), Consider::RejectPast);
		assert_eq!(view.consider_vote(Round(1000), SetId(0)), Consider::RejectPast);

		assert_eq!(view.consider_vote(Round(99), SetId(1)), Consider::Accept);
		assert_eq!(view.consider_vote(Round(100), SetId(1)), Consider::Accept);
		assert_eq!(view.consider_vote(Round(101), SetId(1)), Consider::Accept);

		assert_eq!(view.consider_vote(Round(102), SetId(1)), Consider::RejectFuture);
		assert_eq!(view.consider_vote(Round(1), SetId(2)), Consider::RejectFuture);
		assert_eq!(view.consider_vote(Round(1000), SetId(2)), Consider::RejectFuture);
	}

	#[test]
	fn view_global_message_rules() {
		let view = View { round: Round(100), set_id: SetId(2), last_commit: Some(1000u64) };

		assert_eq!(view.consider_global(SetId(3), 1), Consider::RejectFuture);
		assert_eq!(view.consider_global(SetId(3), 1000), Consider::RejectFuture);
		assert_eq!(view.consider_global(SetId(3), 10000), Consider::RejectFuture);

		assert_eq!(view.consider_global(SetId(1), 1), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(1), 1000), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(1), 10000), Consider::RejectPast);

		assert_eq!(view.consider_global(SetId(2), 1), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(2), 1000), Consider::RejectPast);
		assert_eq!(view.consider_global(SetId(2), 1001), Consider::Accept);
		assert_eq!(view.consider_global(SetId(2), 10000), Consider::Accept);
	}

	#[test]
	fn unknown_peer_cannot_be_updated() {
		let mut peers = Peers::default();
		let id = PeerId::random();

		let update =
			NeighborPacket { round: Round(5), set_id: SetId(10), commit_finalized_height: 50 };

		let res = peers.update_peer_state(&id, update.clone());
		assert!(res.unwrap().is_none());

		// connect & disconnect.
		peers.new_peer(id, ObservedRole::Authority);
		peers.peer_disconnected(&id);

		let res = peers.update_peer_state(&id, update.clone());
		assert!(res.unwrap().is_none());
	}

	#[test]
	fn update_peer_state() {
		let update1 =
			NeighborPacket { round: Round(5), set_id: SetId(10), commit_finalized_height: 50u32 };

		let update2 =
			NeighborPacket { round: Round(6), set_id: SetId(10), commit_finalized_height: 60 };

		let update3 =
			NeighborPacket { round: Round(2), set_id: SetId(11), commit_finalized_height: 61 };

		let update4 =
			NeighborPacket { round: Round(3), set_id: SetId(11), commit_finalized_height: 80 };

		let mut peers = Peers::default();
		let id = PeerId::random();

		peers.new_peer(id, ObservedRole::Authority);

		let mut check_update = move |update: NeighborPacket<_>| {
			let view = peers.update_peer_state(&id, update.clone()).unwrap().unwrap();
			assert_eq!(view.round, update.round);
			assert_eq!(view.set_id, update.set_id);
			assert_eq!(view.last_commit, Some(update.commit_finalized_height));
		};

		check_update(update1);
		check_update(update2);
		check_update(update3);
		check_update(update4);
	}

	#[test]
	fn invalid_view_change() {
		let mut peers = Peers::default();

		let id = PeerId::random();
		peers.new_peer(id, ObservedRole::Authority);

		peers
			.update_peer_state(
				&id,
				NeighborPacket { round: Round(10), set_id: SetId(10), commit_finalized_height: 10 },
			)
			.unwrap()
			.unwrap();

		let mut check_update = move |update: NeighborPacket<_>| {
			let err = peers.update_peer_state(&id, update.clone()).unwrap_err();
			assert_eq!(err, Misbehavior::InvalidViewChange);
		};

		// round moves backwards.
		check_update(NeighborPacket {
			round: Round(9),
			set_id: SetId(10),
			commit_finalized_height: 10,
		});
		// commit finalized height moves backwards.
		check_update(NeighborPacket {
			round: Round(10),
			set_id: SetId(10),
			commit_finalized_height: 9,
		});
		// set ID moves backwards.
		check_update(NeighborPacket {
			round: Round(10),
			set_id: SetId(9),
			commit_finalized_height: 10,
		});
	}

	#[test]
	fn messages_not_expired_immediately() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		let set_id = 1;

		val.note_set(SetId(set_id), Vec::new(), |_, _| {});

		for round_num in 1u64..10 {
			val.note_round(Round(round_num), |_, _| {});
		}

		{
			let mut is_expired = val.message_expired();
			let last_kept_round = 10u64 - KEEP_RECENT_ROUNDS as u64 - 1;

			// messages from old rounds are expired.
			for round_num in 1u64..last_kept_round {
				let topic = communication::round_topic::<Block>(round_num, 1);
				assert!(is_expired(topic, &[1, 2, 3]));
			}

			// messages from not-too-old rounds are not expired.
			for round_num in last_kept_round..10 {
				let topic = communication::round_topic::<Block>(round_num, 1);
				assert!(!is_expired(topic, &[1, 2, 3]));
			}
		}
	}

	#[test]
	fn message_from_unknown_authority_discarded() {
		assert!(cost::UNKNOWN_VOTER != cost::BAD_SIGNATURE);

		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);
		let set_id = 1;
		let auth = AuthorityId::unchecked_from([1u8; 32]);
		let peer = PeerId::random();

		val.note_set(SetId(set_id), vec![auth.clone()], |_, _| {});
		val.note_round(Round(1), |_, _| {});

		let inner = val.inner.read();
		let unknown_voter = inner.validate_round_message(
			&peer,
			&VoteMessage {
				round: Round(1),
				set_id: SetId(set_id),
				message: SignedMessage::<Header> {
					message: finality_grandpa::Message::Prevote(finality_grandpa::Prevote {
						target_hash: Default::default(),
						target_number: 10,
					}),
					signature: UncheckedFrom::unchecked_from([1; 64]),
					id: UncheckedFrom::unchecked_from([2u8; 32]),
				},
			},
		);

		let bad_sig = inner.validate_round_message(
			&peer,
			&VoteMessage {
				round: Round(1),
				set_id: SetId(set_id),
				message: SignedMessage::<Header> {
					message: finality_grandpa::Message::Prevote(finality_grandpa::Prevote {
						target_hash: Default::default(),
						target_number: 10,
					}),
					signature: UncheckedFrom::unchecked_from([1; 64]),
					id: auth.clone(),
				},
			},
		);

		assert_eq!(unknown_voter, Action::Discard(cost::UNKNOWN_VOTER));
		assert_eq!(bad_sig, Action::Discard(cost::BAD_SIGNATURE));
	}

	#[test]
	fn unsolicited_catch_up_messages_discarded() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		let set_id = 1;
		let auth = AuthorityId::unchecked_from([1u8; 32]);
		let peer = PeerId::random();

		val.note_set(SetId(set_id), vec![auth.clone()], |_, _| {});
		val.note_round(Round(1), |_, _| {});

		let validate_catch_up = || {
			let mut inner = val.inner.write();
			inner.validate_catch_up_message(
				&peer,
				&FullCatchUpMessage {
					set_id: SetId(set_id),
					message: finality_grandpa::CatchUp {
						round_number: 10,
						prevotes: Default::default(),
						precommits: Default::default(),
						base_hash: Default::default(),
						base_number: Default::default(),
					},
				},
			)
		};

		// the catch up is discarded because we have no pending request
		assert_eq!(validate_catch_up(), Action::Discard(cost::OUT_OF_SCOPE_MESSAGE));

		let noted = val.inner.write().note_catch_up_request(
			&peer,
			&CatchUpRequestMessage { set_id: SetId(set_id), round: Round(10) },
		);

		assert!(noted.0);

		// catch up is allowed because we have requested it, but it's rejected
		// because it's malformed (empty prevotes and precommits)
		assert_eq!(validate_catch_up(), Action::Discard(cost::MALFORMED_CATCH_UP));
	}

	#[test]
	fn unanswerable_catch_up_requests_discarded() {
		// create voter set state with round 2 completed
		let set_state: SharedVoterSetState<Block> = {
			let mut completed_rounds = voter_set_state().read().completed_rounds();

			completed_rounds.push(environment::CompletedRound {
				number: 2,
				state: finality_grandpa::round::State::genesis(Default::default()),
				base: Default::default(),
				votes: Default::default(),
			});

			let mut current_rounds = environment::CurrentRounds::<Block>::new();
			current_rounds.insert(3, environment::HasVoted::No);

			let set_state =
				environment::VoterSetState::<Block>::Live { completed_rounds, current_rounds };

			set_state.into()
		};

		let (val, _) = GossipValidator::<Block>::new(config(), set_state.clone(), None, None);

		let set_id = 1;
		let auth = AuthorityId::unchecked_from([1u8; 32]);
		let peer = PeerId::random();

		val.note_set(SetId(set_id), vec![auth.clone()], |_, _| {});
		val.note_round(Round(3), |_, _| {});

		// add the peer making the request to the validator,
		// otherwise it is discarded
		let mut inner = val.inner.write();
		inner.peers.new_peer(peer, ObservedRole::Authority);

		let res = inner.handle_catch_up_request(
			&peer,
			CatchUpRequestMessage { set_id: SetId(set_id), round: Round(10) },
			&set_state,
		);

		// we're at round 3, a catch up request for round 10 is out of scope
		assert!(res.0.is_none());
		assert_eq!(res.1, Action::Discard(cost::OUT_OF_SCOPE_MESSAGE));

		let res = inner.handle_catch_up_request(
			&peer,
			CatchUpRequestMessage { set_id: SetId(set_id), round: Round(2) },
			&set_state,
		);

		// a catch up request for round 2 should be answered successfully
		match res.0.unwrap() {
			GossipMessage::CatchUp(catch_up) => {
				assert_eq!(catch_up.set_id, SetId(set_id));
				assert_eq!(catch_up.message.round_number, 2);

				assert_eq!(res.1, Action::Discard(cost::CATCH_UP_REPLY));
			},
			_ => panic!("expected catch up message"),
		};
	}

	#[test]
	fn detects_honest_out_of_scope_catch_requests() {
		let set_state = voter_set_state();
		let (val, _) = GossipValidator::<Block>::new(config(), set_state.clone(), None, None);

		// the validator starts at set id 2
		val.note_set(SetId(2), Vec::new(), |_, _| {});

		// add the peer making the request to the validator,
		// otherwise it is discarded
		let peer = PeerId::random();
		val.inner.write().peers.new_peer(peer, ObservedRole::Authority);

		let send_request = |set_id, round| {
			let mut inner = val.inner.write();
			inner.handle_catch_up_request(
				&peer,
				CatchUpRequestMessage { set_id: SetId(set_id), round: Round(round) },
				&set_state,
			)
		};

		let assert_res = |res: (Option<_>, Action<_>), honest| {
			assert!(res.0.is_none());
			assert_eq!(
				res.1,
				if honest {
					Action::Discard(cost::HONEST_OUT_OF_SCOPE_CATCH_UP)
				} else {
					Action::Discard(Misbehavior::OutOfScopeMessage.cost())
				},
			);
		};

		// the validator is at set id 2 and round 0. requests for set id 1
		// should not be answered but they should be considered an honest
		// mistake
		assert_res(send_request(1, 1), true);

		assert_res(send_request(1, 10), true);

		// requests for set id 0 should be considered out of scope
		assert_res(send_request(0, 1), false);

		assert_res(send_request(0, 10), false);

		// after the validator progresses further than CATCH_UP_THRESHOLD in set
		// id 2, any request for set id 1 should no longer be considered an
		// honest mistake.
		val.note_round(Round(3), |_, _| {});

		assert_res(send_request(1, 1), false);

		assert_res(send_request(1, 2), false);
	}

	#[test]
	fn issues_catch_up_request_on_neighbor_packet_import() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		// the validator starts at set id 1.
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// add the peer making the request to the validator,
		// otherwise it is discarded.
		let peer = PeerId::random();
		val.inner.write().peers.new_peer(peer, ObservedRole::Authority);

		let import_neighbor_message = |set_id, round| {
			let (_, _, catch_up_request, _) = val.inner.write().import_neighbor_message(
				&peer,
				NeighborPacket {
					round: Round(round),
					set_id: SetId(set_id),
					commit_finalized_height: 42,
				},
			);

			catch_up_request
		};

		// importing a neighbor message from a peer in the same set in a later
		// round should lead to a catch up request for the previous round.
		match import_neighbor_message(1, 42) {
			Some(GossipMessage::CatchUpRequest(request)) => {
				assert_eq!(request.set_id, SetId(1));
				assert_eq!(request.round, Round(41));
			},
			_ => panic!("expected catch up message"),
		}

		// we note that we're at round 41.
		val.note_round(Round(41), |_, _| {});

		// if we import a neighbor message within CATCH_UP_THRESHOLD then we
		// won't request a catch up.
		match import_neighbor_message(1, 42) {
			None => {},
			_ => panic!("expected no catch up message"),
		}

		// or if the peer is on a lower round.
		match import_neighbor_message(1, 40) {
			None => {},
			_ => panic!("expected no catch up message"),
		}

		// we also don't request a catch up if the peer is in a different set.
		match import_neighbor_message(2, 42) {
			None => {},
			_ => panic!("expected no catch up message"),
		}
	}

	#[test]
	fn doesnt_send_catch_up_requests_when_disabled() {
		// we create a gossip validator with catch up requests disabled.
		let config = {
			let mut c = config();

			// if the observer protocol is enabled and we are not an authority,
			// then we don't issue any catch-up requests.
			c.local_role = Role::Full;
			c.observer_enabled = true;

			c
		};

		let (val, _) = GossipValidator::<Block>::new(config, voter_set_state(), None, None);

		// the validator starts at set id 1.
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// add the peer making the request to the validator,
		// otherwise it is discarded.
		let peer = PeerId::random();
		val.inner.write().peers.new_peer(peer, ObservedRole::Authority);

		// importing a neighbor message from a peer in the same set in a later
		// round should lead to a catch up request but since they're disabled
		// we should get `None`.
		let (_, _, catch_up_request, _) = val.inner.write().import_neighbor_message(
			&peer,
			NeighborPacket { round: Round(42), set_id: SetId(1), commit_finalized_height: 50 },
		);

		match catch_up_request {
			None => {},
			_ => panic!("expected no catch up message"),
		}
	}

	#[test]
	fn doesnt_send_catch_up_requests_to_non_authorities_when_observer_enabled() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		// the validator starts at set id 1.
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// add the peers making the requests to the validator,
		// otherwise it is discarded.
		let peer_authority = PeerId::random();
		let peer_full = PeerId::random();

		val.inner.write().peers.new_peer(peer_authority, ObservedRole::Authority);
		val.inner.write().peers.new_peer(peer_full, ObservedRole::Full);

		let import_neighbor_message = |peer| {
			let (_, _, catch_up_request, _) = val.inner.write().import_neighbor_message(
				&peer,
				NeighborPacket { round: Round(42), set_id: SetId(1), commit_finalized_height: 50 },
			);

			catch_up_request
		};

		// importing a neighbor message from a peer in the same set in a later
		// round should lead to a catch up request but since the node is not an
		// authority we should get `None`.
		if import_neighbor_message(peer_full).is_some() {
			panic!("expected no catch up message");
		}

		// importing the same neighbor message from a peer who is an authority
		// should lead to a catch up request.
		match import_neighbor_message(peer_authority) {
			Some(GossipMessage::CatchUpRequest(request)) => {
				assert_eq!(request.set_id, SetId(1));
				assert_eq!(request.round, Round(41));
			},
			_ => panic!("expected catch up message"),
		}
	}

	#[test]
	fn sends_catch_up_requests_to_non_authorities_when_observer_disabled() {
		let config = {
			let mut c = config();

			// if the observer protocol is disable any full-node should be able
			// to answer catch-up requests.
			c.observer_enabled = false;

			c
		};

		let (val, _) = GossipValidator::<Block>::new(config, voter_set_state(), None, None);

		// the validator starts at set id 1.
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// add the peer making the requests to the validator, otherwise it is
		// discarded.
		let peer_full = PeerId::random();
		val.inner.write().peers.new_peer(peer_full, ObservedRole::Full);

		let (_, _, catch_up_request, _) = val.inner.write().import_neighbor_message(
			&peer_full,
			NeighborPacket { round: Round(42), set_id: SetId(1), commit_finalized_height: 50 },
		);

		// importing a neighbor message from a peer in the same set in a later
		// round should lead to a catch up request, the node is not an
		// authority, but since the observer protocol is disabled we should
		// issue a catch-up request to it anyway.
		match catch_up_request {
			Some(GossipMessage::CatchUpRequest(request)) => {
				assert_eq!(request.set_id, SetId(1));
				assert_eq!(request.round, Round(41));
			},
			_ => panic!("expected catch up message"),
		}
	}

	#[test]
	fn doesnt_expire_next_round_messages() {
		// NOTE: this is a regression test
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		// the validator starts at set id 1.
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// we are at round 10
		val.note_round(Round(9), |_, _| {});
		val.note_round(Round(10), |_, _| {});

		let mut is_expired = val.message_expired();

		// we accept messages from rounds 9, 10 and 11
		// therefore neither of those should be considered expired
		for round in &[9, 10, 11] {
			assert!(!is_expired(communication::round_topic::<Block>(*round, 1), &[]))
		}
	}

	#[test]
	fn progressively_gossips_to_more_peers_as_round_duration_increases() {
		let mut config = config();
		config.gossip_duration = Duration::from_secs(300); // Set to high value to prevent test race
		let round_duration = config.gossip_duration * ROUND_DURATION;

		let (val, _) = GossipValidator::<Block>::new(config, voter_set_state(), None, None);

		// the validator start at set id 0
		val.note_set(SetId(0), Vec::new(), |_, _| {});

		// add 60 peers, 30 authorities and 30 full nodes
		let mut authorities = Vec::new();
		authorities.resize_with(30, || PeerId::random());

		let mut full_nodes = Vec::new();
		full_nodes.resize_with(30, || PeerId::random());

		for i in 0..30 {
			val.inner.write().peers.new_peer(authorities[i], ObservedRole::Authority);

			val.inner.write().peers.new_peer(full_nodes[i], ObservedRole::Full);
		}

		let test = |rounds_elapsed, peers| {
			// rewind n round durations
			val.inner.write().local_view.as_mut().unwrap().round_start = Instant::now() -
				Duration::from_millis(
					(round_duration.as_millis() as f32 * rounds_elapsed) as u64,
				);

			val.inner.write().peers.reshuffle();

			let mut message_allowed = val.message_allowed();

			move || {
				let mut allowed = 0;
				for peer in peers {
					if message_allowed(
						peer,
						MessageIntent::Broadcast,
						&communication::round_topic::<Block>(1, 0),
						&[],
					) {
						allowed += 1;
					}
				}
				allowed
			}
		};

		fn trial<F: FnMut() -> usize>(mut test: F) -> usize {
			let mut results = Vec::new();
			let n = 1000;

			for _ in 0..n {
				results.push(test());
			}

			let n = results.len();
			let sum: usize = results.iter().sum();

			sum / n
		}

		let all_peers = authorities.iter().chain(full_nodes.iter()).cloned().collect();

		// on the first attempt we will only gossip to 4 peers, either
		// authorities or full nodes, but we'll guarantee that half of those
		// are authorities
		assert!(trial(test(1.0, &authorities)) >= LUCKY_PEERS / 2);
		assert_eq!(trial(test(1.0, &all_peers)), LUCKY_PEERS);

		// after more than 1.5 round durations have elapsed we should gossip to
		// `sqrt(peers)` we're connected to, but we guarantee that at least 4 of
		// those peers are authorities (plus the `LUCKY_PEERS` from the previous
		// stage)
		assert!(trial(test(PROPAGATION_SOME * 1.1, &authorities)) >= LUCKY_PEERS);
		assert_eq!(
			trial(test(2.0, &all_peers)),
			LUCKY_PEERS + (all_peers.len() as f64).sqrt() as usize,
		);

		// after 3 rounds durations we should gossip to all peers we are
		// connected to
		assert_eq!(trial(test(PROPAGATION_ALL * 1.1, &all_peers)), all_peers.len());
	}

	#[test]
	fn never_gossips_round_messages_to_light_clients() {
		let config = config();
		let round_duration = config.gossip_duration * ROUND_DURATION;
		let (val, _) = GossipValidator::<Block>::new(config, voter_set_state(), None, None);

		// the validator starts at set id 0
		val.note_set(SetId(0), Vec::new(), |_, _| {});

		// add a new light client as peer
		let light_peer = PeerId::random();

		val.inner.write().peers.new_peer(light_peer, ObservedRole::Light);

		assert!(!val.message_allowed()(
			&light_peer,
			MessageIntent::Broadcast,
			&communication::round_topic::<Block>(1, 0),
			&[],
		));

		// we reverse the round start time so that the elapsed time is higher
		// (which should lead to more peers getting the message)
		val.inner.write().local_view.as_mut().unwrap().round_start =
			Instant::now() - round_duration * 10;

		// even after the round has been going for 10 round durations we will never
		// gossip to light clients
		assert!(!val.message_allowed()(
			&light_peer,
			MessageIntent::Broadcast,
			&communication::round_topic::<Block>(1, 0),
			&[],
		));

		// update the peer state and local state wrt commits
		val.inner
			.write()
			.peers
			.update_peer_state(
				&light_peer,
				NeighborPacket { round: Round(1), set_id: SetId(0), commit_finalized_height: 1 },
			)
			.unwrap();

		val.note_commit_finalized(Round(1), SetId(0), 2, |_, _| {});

		let commit = {
			let commit = finality_grandpa::CompactCommit {
				target_hash: H256::random(),
				target_number: 2,
				precommits: Vec::new(),
				auth_data: Vec::new(),
			};

			communication::gossip::GossipMessage::<Block>::Commit(
				communication::gossip::FullCommitMessage {
					round: Round(2),
					set_id: SetId(0),
					message: commit,
				},
			)
			.encode()
		};

		// global messages are gossiped to light clients though
		assert!(val.message_allowed()(
			&light_peer,
			MessageIntent::Broadcast,
			&communication::global_topic::<Block>(0),
			&commit,
		));
	}

	#[test]
	fn only_gossip_commits_to_peers_on_same_set() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		// the validator starts at set id 1
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// add a new peer at set id 1
		let peer1 = PeerId::random();

		val.inner.write().peers.new_peer(peer1, ObservedRole::Authority);

		val.inner
			.write()
			.peers
			.update_peer_state(
				&peer1,
				NeighborPacket { round: Round(1), set_id: SetId(1), commit_finalized_height: 1 },
			)
			.unwrap();

		// peer2 will default to set id 0
		let peer2 = PeerId::random();
		val.inner.write().peers.new_peer(peer2, ObservedRole::Authority);

		// create a commit for round 1 of set id 1
		// targeting a block at height 2
		let commit = {
			let commit = finality_grandpa::CompactCommit {
				target_hash: H256::random(),
				target_number: 2,
				precommits: Vec::new(),
				auth_data: Vec::new(),
			};

			communication::gossip::GossipMessage::<Block>::Commit(
				communication::gossip::FullCommitMessage {
					round: Round(1),
					set_id: SetId(1),
					message: commit,
				},
			)
			.encode()
		};

		// note the commit in the validator
		val.note_commit_finalized(Round(1), SetId(1), 2, |_, _| {});

		let mut message_allowed = val.message_allowed();

		// the commit should be allowed to peer 1
		assert!(message_allowed(
			&peer1,
			MessageIntent::Broadcast,
			&communication::global_topic::<Block>(1),
			&commit,
		));

		// but disallowed to peer 2 since the peer is on set id 0
		// the commit should be allowed to peer 1
		assert!(!message_allowed(
			&peer2,
			MessageIntent::Broadcast,
			&communication::global_topic::<Block>(1),
			&commit,
		));
	}

	#[test]
	fn expire_commits_from_older_rounds() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		let commit = |round, set_id, target_number| {
			let commit = finality_grandpa::CompactCommit {
				target_hash: H256::random(),
				target_number,
				precommits: Vec::new(),
				auth_data: Vec::new(),
			};

			communication::gossip::GossipMessage::<Block>::Commit(
				communication::gossip::FullCommitMessage {
					round: Round(round),
					set_id: SetId(set_id),
					message: commit,
				},
			)
			.encode()
		};

		// note the beginning of a new set with id 1
		val.note_set(SetId(1), Vec::new(), |_, _| {});

		// note a commit for round 1 in the validator
		// finalizing a block at height 2
		val.note_commit_finalized(Round(1), SetId(1), 2, |_, _| {});

		let mut message_expired = val.message_expired();

		// a commit message for round 1 that finalizes the same height as we
		// have observed previously should not be expired
		assert!(!message_expired(communication::global_topic::<Block>(1), &commit(1, 1, 2),));

		// it should be expired if it is for a lower block
		assert!(message_expired(communication::global_topic::<Block>(1), &commit(1, 1, 1)));

		// or the same block height but from the previous round
		assert!(message_expired(communication::global_topic::<Block>(1), &commit(0, 1, 2)));
	}

	#[test]
	fn allow_noting_different_authorities_for_same_set() {
		let (val, _) = GossipValidator::<Block>::new(config(), voter_set_state(), None, None);

		let a1 = vec![UncheckedFrom::unchecked_from([0; 32])];
		val.note_set(SetId(1), a1.clone(), |_, _| {});

		assert_eq!(val.inner().read().authorities, a1);

		let a2 =
			vec![UncheckedFrom::unchecked_from([1; 32]), UncheckedFrom::unchecked_from([2; 32])];
		val.note_set(SetId(1), a2.clone(), |_, _| {});

		assert_eq!(val.inner().read().authorities, a2);
	}
}
