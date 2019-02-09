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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use fnv::FnvHashMap;
use libp2p::{core::swarm::ConnectedPoint, Multiaddr, PeerId};
use log::{debug, info, trace, warn};
use serde_derive::{Serialize, Deserialize};
use std::{cmp, fs};
use std::io::{Read, Cursor, Error as IoError, ErrorKind as IoErrorKind, Write, BufReader, BufWriter};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

/// For each address we're connected to, a period of this duration increases the score by 1.
const CONNEC_DURATION_PER_SCORE: Duration = Duration::from_secs(10);
/// Maximum number of addresses for a given peer. If there are more than this number of addresses,
/// the ones with a lower score will be removed.
const MAX_ADDRESSES_PER_PEER: usize = 10;
/// Maximum value for the score.
const MAX_SCORE: u32 = 100;
/// When we successfully connect to a node, raises its score to the given minimum value.
const CONNECTED_MINIMUM_SCORE: u32 = 20;
/// Initial score that a node discovered through Kademlia receives, where we have a hint that the
/// node is reachable.
const DISCOVERY_INITIAL_SCORE_CONNECTABLE: u32 = 15;
/// Initial score that a node discovered through Kademlia receives, without any hint.
const DISCOVERY_INITIAL_SCORE: u32 = 10;
/// Score adjustement when we fail to connect to an address.
const SCORE_DIFF_ON_FAILED_TO_CONNECT: i32 = -1;
/// Default time-to-live for addresses discovered through Kademlia.
/// After this time has elapsed and no connection has succeeded, the address will be removed.
const KADEMLIA_DISCOVERY_EXPIRATION: Duration = Duration::from_secs(2 * 3600);
/// After a successful connection, the TTL is set to a minimum at this amount.
const EXPIRATION_PUSH_BACK_CONNEC: Duration = Duration::from_secs(2 * 3600);
/// Initial score that a bootstrap node receives when registered.
const BOOTSTRAP_NODE_SCORE: u32 = 100;
/// Time to live of a boostrap node. This only applies if you start the node later *without*
/// that bootstrap node configured anymore.
const BOOTSTRAP_NODE_EXPIRATION: Duration = Duration::from_secs(24 * 3600);
/// The first time we fail to connect to an address, wait this duration before trying again.
const FIRST_CONNECT_FAIL_BACKOFF: Duration = Duration::from_secs(2);
/// Every time we fail to connect to an address, multiply the backoff by this constant.
const FAIL_BACKOFF_MULTIPLIER: u32 = 2;
/// We need a maximum value for the backoff, overwise we risk an overflow.
const MAX_BACKOFF: Duration = Duration::from_secs(30 * 60);

/// Stores information about the topology of the network.
#[derive(Debug)]
pub struct NetTopology {
	/// The actual storage. Never contains a key for `local_peer_id`.
	store: FnvHashMap<PeerId, PeerInfo>,
	/// Optional path to the file that caches the serialized version of `store`.
	cache_path: Option<PathBuf>,
	/// PeerId of the local node.
	local_peer_id: PeerId,
}

impl NetTopology {
	/// Initializes a new `NetTopology` that isn't tied to any file.
	///
	/// `flush_to_disk()` will be a no-op.
	#[inline]
	pub fn memory(local_peer_id: PeerId) -> NetTopology {
		NetTopology {
			store: Default::default(),
			cache_path: None,
			local_peer_id,
		}
	}

	/// Builds a `NetTopology` that will use `path` as a cache.
	///
	/// This function tries to load a known topology from the file. If the file doesn't exist
	/// or contains garbage data, the execution still continues.
	///
	/// Calling `flush_to_disk()` in the future writes to the given path.
	pub fn from_file<P: AsRef<Path>>(local_peer_id: PeerId, path: P) -> NetTopology {
		let path = path.as_ref();
		debug!(target: "sub-libp2p", "Initializing peer store for JSON file {:?}", path);
		let store = try_load(path, &local_peer_id);
		NetTopology {
			store,
			cache_path: Some(path.to_owned()),
			local_peer_id,
		}
	}

	/// Writes the topology into the path passed to `from_file`.
	///
	/// No-op if the object was created with `memory()`.
	pub fn flush_to_disk(&mut self) -> Result<(), IoError> {
		let path = match self.cache_path {
			Some(ref p) => p,
			None => return Ok(())
		};

		let file = fs::File::create(path)?;
		// TODO: the capacity of the BufWriter is kind of arbitrary ; decide better
		serialize(BufWriter::with_capacity(1024 * 1024, file), &mut self.store)
	}

	/// Returns the number of peers in the topology, excluding the local peer.
	#[inline]
	pub fn num_peers(&self) -> usize {
		self.store.len()
	}

	/// Perform a cleanup pass, removing all obsolete addresses and peers.
	///
	/// This should be done from time to time.
	pub fn cleanup(&mut self) {
		let now_systime = SystemTime::now();
		self.store.retain(|_, peer| {
			let new_addrs = peer.addrs
				.drain(..)
				.filter(|a| a.expires > now_systime || a.is_connected())
				.collect();
			peer.addrs = new_addrs;
			!peer.addrs.is_empty()
		});
	}

	/// Returns a list of all the known addresses of peers, ordered by the
	/// order in which we should attempt to connect to them.
	///
	/// Because of expiration and back-off mechanisms, this list can grow
	/// by itself over time. The `Instant` that is returned corresponds to
	/// the earlier known time when a new entry will be added automatically to
	/// the list.
	pub fn addrs_to_attempt(&mut self) -> (impl Iterator<Item = (&PeerId, &Multiaddr)>, Instant) {
		// TODO: optimize
		let now = Instant::now();
		let now_systime = SystemTime::now();
		let mut instant = now + Duration::from_secs(3600);
		let mut addrs_out = Vec::new();

		let mut peer_addrs = Vec::new();

		'peer_loop: for (peer, info) in &mut self.store {
			peer_addrs.clear();

			for addr in &mut info.addrs {
				let (score, is_connected) = addr.score_and_is_connected();
				if is_connected {
					continue 'peer_loop
				}
				if score == 0 || addr.expires < now_systime {
					continue
				}
				if addr.back_off_until > now {
					instant = cmp::min(instant, addr.back_off_until);
					continue
				}

				peer_addrs.push(((peer, &addr.addr), score));
			}

			for val in peer_addrs.drain(..) {
				addrs_out.push(val);
			}
		}

		addrs_out.sort_by(|a, b| b.1.cmp(&a.1));
		(addrs_out.into_iter().map(|a| a.0), instant)
	}

	/// Adds an address corresponding to a boostrap node.
	///
	/// We assume that the address is valid, so its score starts very high.
	pub fn add_bootstrap_addr(&mut self, peer: &PeerId, addr: Multiaddr) {
		if *peer == self.local_peer_id {
			return
		}

		let now_systime = SystemTime::now();
		let now = Instant::now();

		let peer = peer_access(&mut self.store, peer);

		let mut found = false;
		let new_addrs = peer.addrs
			.drain(..)
			.filter_map(|a| {
				if a.expires < now_systime && !a.is_connected() {
					return None
				}
				if a.addr == addr {
					found = true;
				}
				Some(a)
			})
			.collect();
		peer.addrs = new_addrs;

		if !found {
			peer.addrs.push(Addr {
				addr,
				expires: now_systime + BOOTSTRAP_NODE_EXPIRATION,
				back_off_until: now,
				next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
				score: AddrScore {
					connected_since: None,
					score: BOOTSTRAP_NODE_SCORE,
					latest_score_update: now,
				},
			});
		}
	}

	/// Indicates the topology that we have discovered new addresses for a given node.
	///
	/// Returns `true` if the topology has changed in some way. Returns `false` if calling this
	/// method was a no-op.
	pub fn add_discovered_addrs<I>(
		&mut self,
		peer_id: &PeerId,
		addrs: I,
	) -> bool
		where I: Iterator<Item = (Multiaddr, bool)> {
		if *peer_id == self.local_peer_id {
			return false
		}

		let mut addrs: Vec<_> = addrs.collect();

		if addrs.len() > 40 {
			warn!(target: "sub-libp2p", "Attempt to add more than 40 addresses for {:?}", peer_id);
			addrs.truncate(40);
		}

		let now_systime = SystemTime::now();
		let now = Instant::now();

		let peer = peer_access(&mut self.store, peer_id);

		let new_addrs = peer.addrs
			.drain(..)
			.filter(|a| {
				if a.expires < now_systime && !a.is_connected() {
					return false
				}
				addrs.retain(|(addr, _)| *addr != a.addr);
				true
			})
			.collect();
		peer.addrs = new_addrs;

		let mut anything_changed = false;

		if !addrs.is_empty() {
			anything_changed = true;
			trace!(
				target: "sub-libp2p",
				"Peer store: adding addresses {:?} for {:?}",
				addrs,
				peer_id,
			);
		}

		'addrs_inserter: for (addr, connectable) in addrs {
			let initial_score = if connectable {
				DISCOVERY_INITIAL_SCORE_CONNECTABLE
			} else {
				DISCOVERY_INITIAL_SCORE
			};

			// Enforce `MAX_ADDRESSES_PER_PEER` before inserting, or skip this entry.
			while peer.addrs.len() >= MAX_ADDRESSES_PER_PEER {
				let pos = peer.addrs.iter_mut().position(|addr| addr.score() <= initial_score);
				if let Some(pos) = pos {
					let _ = peer.addrs.remove(pos);
				} else {
					continue 'addrs_inserter;
				}
			}

			// `addrs` can contain duplicates, therefore we would insert the same address twice.
			if peer.addrs.iter().any(|a| a.addr == addr) {
				continue;
			}

			peer.addrs.push(Addr {
				addr,
				expires: now_systime + KADEMLIA_DISCOVERY_EXPIRATION,
				back_off_until: now,
				next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
				score: AddrScore {
					connected_since: None,
					score: initial_score,
					latest_score_update: now,
				},
			});
		}

		anything_changed
	}

	/// Returns the addresses stored for a specific peer.
	#[inline]
	pub fn addresses_of_peer(&mut self, peer: &PeerId) -> Vec<Multiaddr> {
		let peer = if let Some(peer) = self.store.get_mut(peer) {
			peer
		} else {
			return Vec::new()
		};

		let now_st = SystemTime::now();
		let now_is = Instant::now();

		let mut list = peer.addrs.iter_mut().filter_map(move |addr| {
			let (score, connected) = addr.score_and_is_connected();
			if (addr.expires >= now_st && score > 0 && addr.back_off_until < now_is) || connected {
				Some((score, &addr.addr))
			} else {
				None
			}
		}).collect::<Vec<_>>();
		list.sort_by(|a, b| a.0.cmp(&b.0));
		// TODO: meh, optimize
		list.into_iter().map(|(_, addr)| addr.clone()).collect::<Vec<_>>()
	}

	/// Marks the given peer as connected through the given endpoint.
	pub fn set_connected(&mut self, peer: &PeerId, endpoint: &ConnectedPoint) {
		if *peer == self.local_peer_id {
			return
		}

		let addr = match endpoint {
			ConnectedPoint::Dialer { address } => address,
			ConnectedPoint::Listener { .. } => return
		};

		let now = Instant::now();

		// Just making sure that we have an entry for this peer in `store`, but don't use it.
		let _ = peer_access(&mut self.store, peer);

		for (peer_in_store, info_in_store) in self.store.iter_mut() {
			if peer == peer_in_store {
				if let Some(addr) = info_in_store.addrs.iter_mut().find(|a| &a.addr == addr) {
					addr.connected_now(CONNECTED_MINIMUM_SCORE);
					addr.back_off_until = now;
					addr.next_back_off = FIRST_CONNECT_FAIL_BACKOFF;
					continue
				}

				info_in_store.addrs.push(Addr {
					addr: addr.clone(),
					expires: SystemTime::now() + EXPIRATION_PUSH_BACK_CONNEC,
					back_off_until: now,
					next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
					score: AddrScore {
						connected_since: Some(now),
						latest_score_update: now,
						score: CONNECTED_MINIMUM_SCORE,
					},
				});

			} else {
				// Set the score to 0 for any address that matches the one we connected to.
				for addr_in_store in &mut info_in_store.addrs {
					if &addr_in_store.addr == addr {
						addr_in_store.adjust_score(-(MAX_SCORE as i32));
					}
				}
			}
		}
	}

	/// Marks the given peer as disconnected. The endpoint is the one we were connected to.
	pub fn set_disconnected(&mut self, _: &PeerId, endpoint: &ConnectedPoint) {
		let addr = match endpoint {
			ConnectedPoint::Dialer { address } => address,
			ConnectedPoint::Listener { .. } => return
		};

		// Note that we used to have different score values here in the past, but there really
		// isn't much point in doing so in practice.
		let score_diff = -3;

		for info in self.store.values_mut() {
			for a in info.addrs.iter_mut() {
				if &a.addr == addr {
					a.disconnected_now(score_diff);
					a.back_off_until = Instant::now() + a.next_back_off;
					a.next_back_off = cmp::min(a.next_back_off * FAIL_BACKOFF_MULTIPLIER, MAX_BACKOFF);
					let expires_push_back = SystemTime::now() + EXPIRATION_PUSH_BACK_CONNEC;
					if a.expires < expires_push_back {
						a.expires = expires_push_back;
					}
					return
				}
			}
		}
	}

	/// Indicates to the topology that we failed to reach a node when dialing the given address.
	pub fn set_unreachable(&mut self, addr: &Multiaddr) {
		for info in self.store.values_mut() {
			for a in info.addrs.iter_mut() {
				if &a.addr != addr {
					continue
				}

				debug_assert!(!a.is_connected());
				a.adjust_score(SCORE_DIFF_ON_FAILED_TO_CONNECT);
				trace!(target: "sub-libp2p", "Back off for {} = {:?}", addr, a.next_back_off);
				a.back_off_until = Instant::now() + a.next_back_off;
				a.next_back_off = cmp::min(a.next_back_off * FAIL_BACKOFF_MULTIPLIER, MAX_BACKOFF);
			}
		}
	}
}

fn peer_access<'a>(store: &'a mut FnvHashMap<PeerId, PeerInfo>, peer: &PeerId) -> &'a mut PeerInfo {
	// TODO: should be optimizable if HashMap gets a better API
	store.entry(peer.clone()).or_insert_with(Default::default)
}

#[derive(Debug, Clone, Default)]
struct PeerInfo {
	/// Addresses of that peer.
	addrs: Vec<Addr>,
}

#[derive(Debug)]
struct Addr {
	/// The multiaddress.
	addr: Multiaddr,
	/// When the address expires.
	expires: SystemTime,
	next_back_off: Duration,
	/// Don't try to connect to this node until `Instant`.
	back_off_until: Instant,
	score: AddrScore,
}

impl Clone for Addr {
	fn clone(&self) -> Addr {
		Addr {
			addr: self.addr.clone(),
			expires: self.expires,
			next_back_off: self.next_back_off,
			back_off_until: self.back_off_until,
			score: self.score.clone(),
		}
	}
}

#[derive(Debug, Clone)]
struct AddrScore {
	/// If connected, contains the moment when we connected. `None` if we're not connected.
	connected_since: Option<Instant>,
	/// Score of this address. Potentially needs to be updated based on `latest_score_update`.
	score: u32,
	/// When we last updated the score.
	latest_score_update: Instant,
}

impl Addr {
	/// Sets the addr to connected. If the score is lower than the given value, raises it to this
	/// value.
	fn connected_now(&mut self, raise_to_min: u32) {
		let now = Instant::now();
		Addr::flush(&mut self.score, now);
		self.score.connected_since = Some(now);
		if self.score.score < raise_to_min {
			self.score.score = raise_to_min;
		}
	}

	/// Applies a modification to the score.
	fn adjust_score(&mut self, score_diff: i32) {
		Addr::flush(&mut self.score, Instant::now());
		if score_diff >= 0 {
			self.score.score = cmp::min(MAX_SCORE, self.score.score + score_diff as u32);
		} else {
			self.score.score = self.score.score.saturating_sub(-score_diff as u32);
		}
	}

	/// Sets the addr to disconnected and applies a modification to the score.
	fn disconnected_now(&mut self, score_diff: i32) {
		Addr::flush(&mut self.score, Instant::now());
		self.score.connected_since = None;
		if score_diff >= 0 {
			self.score.score = cmp::min(MAX_SCORE, self.score.score + score_diff as u32);
		} else {
			self.score.score = self.score.score.saturating_sub(-score_diff as u32);
		}
	}

	/// Returns true if we are connected to this addr.
	fn is_connected(&self) -> bool {
		self.score.connected_since.is_some()
	}

	/// Returns the score, and true if we are connected to this addr.
	fn score_and_is_connected(&mut self) -> (u32, bool) {
		Addr::flush(&mut self.score, Instant::now());
		let is_connected = self.score.connected_since.is_some();
		(self.score.score, is_connected)
	}

	/// Updates `score` and `latest_score_update`, and returns the score.
	fn score(&mut self) -> u32 {
		Addr::flush(&mut self.score, Instant::now());
		self.score.score
	}

	fn flush(score: &mut AddrScore, now: Instant) {
		if let Some(connected_since) = score.connected_since {
			let potential_score: u32 = div_dur_with_dur(now - connected_since, CONNEC_DURATION_PER_SCORE);
			// We flush when we connect to an address.
			debug_assert!(score.latest_score_update >= connected_since);
			let effective_score: u32 =
				div_dur_with_dur(score.latest_score_update - connected_since, CONNEC_DURATION_PER_SCORE);
			let to_add = potential_score.saturating_sub(effective_score);
			score.score = cmp::min(MAX_SCORE, score.score + to_add);
		}

		score.latest_score_update = now;
	}
}

/// Divides a `Duration` with a `Duration`. This exists in the stdlib but isn't stable yet.
// TODO: remove this function once stable
fn div_dur_with_dur(a: Duration, b: Duration) -> u32 {
	let a_ms = a.as_secs() * 1_000_000 + u64::from(a.subsec_micros());
	let b_ms = b.as_secs() * 1_000_000 + u64::from(b.subsec_micros());
	(a_ms / b_ms) as u32
}

/// Serialized version of a `PeerInfo`. Suitable for storage in the cache file.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SerializedPeerInfo {
	addrs: Vec<SerializedAddr>,
}

/// Serialized version of an `Addr`. Suitable for storage in the cache file.
#[derive(Debug, Clone, Serialize, Deserialize)]
struct SerializedAddr {
	addr: String,
	expires: SystemTime,
	score: u32,
}

impl<'a> From<&'a mut Addr> for SerializedAddr {
	fn from(addr: &'a mut Addr) -> SerializedAddr {
		SerializedAddr {
			addr: addr.addr.to_string(),
			expires: addr.expires,
			score: addr.score(),
		}
	}
}

/// Attempts to load storage from a file.
/// Ignores any entry equal to `local_peer_id`.
/// Deletes the file and returns an empty map if the file doesn't exist, cannot be opened
/// or is corrupted.
fn try_load(path: impl AsRef<Path>, local_peer_id: &PeerId) -> FnvHashMap<PeerId, PeerInfo> {
	let path = path.as_ref();
	if !path.exists() {
		debug!(target: "sub-libp2p", "Peer storage file {:?} doesn't exist", path);
		return Default::default()
	}

	let mut file = match fs::File::open(path) {
		// TODO: the capacity of the BufReader is kind of arbitrary ; decide better
		Ok(f) => BufReader::with_capacity(1024 * 1024, f),
		Err(err) => {
			warn!(target: "sub-libp2p", "Failed to open peer storage file: {:?}", err);
			info!(target: "sub-libp2p", "Deleting peer storage file {:?}", path);
			let _ = fs::remove_file(path);
			return Default::default()
		}
	};

	// We want to support empty files (and treat them as an empty recordset). Unfortunately
	// `serde_json` will always produce an error if we do this ("unexpected EOF at line 0
	// column 0"). Therefore we start by reading one byte from the file in order to check
	// for EOF.

	let mut first_byte = [0];
	let num_read = match file.read(&mut first_byte) {
		Ok(f) => f,
		Err(err) => {
			// TODO: DRY
			warn!(target: "sub-libp2p", "Failed to read peer storage file: {:?}", err);
			info!(target: "sub-libp2p", "Deleting peer storage file {:?}", path);
			let _ = fs::remove_file(path);
			return Default::default()
		}
	};

	if num_read == 0 {
		// File is empty.
		debug!(target: "sub-libp2p", "Peer storage file {:?} is empty", path);
		Default::default()

	} else {
		let data = Cursor::new(first_byte).chain(file);
		match serde_json::from_reader::<_, serde_json::Value>(data) {
			Ok(serde_json::Value::Null) => Default::default(),
			Ok(serde_json::Value::Object(map)) =>
				deserialize_tolerant(map.into_iter(), local_peer_id),
			Ok(_) | Err(_) => {
				// The `Ok(_)` case means that the file doesn't contain a map.
				let _ = fs::remove_file(path);
				Default::default()
			},
		}
	}
}

/// Attempts to turn a deserialized version of the storage into the final version.
///
/// Skips entries that are invalid or equal to `local_peer_id`.
fn deserialize_tolerant(
	iter: impl Iterator<Item = (String, serde_json::Value)>,
	local_peer_id: &PeerId
) -> FnvHashMap<PeerId, PeerInfo> {
	let now = Instant::now();
	let now_systime = SystemTime::now();

	let mut out = FnvHashMap::default();
	for (peer, info) in iter {
		let peer: PeerId = match peer.parse() {
			Ok(p) => p,
			Err(_) => continue,
		};

		if &peer == local_peer_id {
			continue
		}

		let info: SerializedPeerInfo = match serde_json::from_value(info) {
			Ok(i) => i,
			Err(_) => continue,
		};

		let mut addrs = Vec::with_capacity(info.addrs.len());
		for addr in info.addrs {
			let multiaddr = match addr.addr.parse() {
				Ok(a) => a,
				Err(_) => continue,
			};

			if addr.expires < now_systime {
				continue
			}

			addrs.push(Addr {
				addr: multiaddr,
				expires: addr.expires,
				next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
				back_off_until: now,
				score: AddrScore {
					connected_since: None,
					score: addr.score,
					latest_score_update: now,
				},
			});
		}

		if addrs.is_empty() {
			continue
		}

		out.insert(peer, PeerInfo { addrs });
	}

	out
}

/// Attempts to turn a deserialized version of the storage into the final version.
///
/// Skips entries that are invalid or expired.
fn serialize<W: Write>(out: W, map: &mut FnvHashMap<PeerId, PeerInfo>) -> Result<(), IoError> {
	let now = SystemTime::now();
	let array: FnvHashMap<_, _> = map.iter_mut().filter_map(|(peer, info)| {
		if info.addrs.is_empty() {
			return None
		}

		let peer = peer.to_base58();
		let info = SerializedPeerInfo {
			addrs: info.addrs.iter_mut()
				.filter_map(|a| if a.expires > now || a.is_connected() {
					Some(a.into())
				} else {
					None
				})
				.collect(),
		};

		Some((peer, info))
	}).collect();

	serde_json::to_writer_pretty(out, &array)
		.map_err(|err| IoError::new(IoErrorKind::Other, err))
}
