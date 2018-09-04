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
use parking_lot::Mutex;
use libp2p::{Multiaddr, PeerId};
use serde_json;
use std::{cmp, fs};
use std::io::{Read, Cursor, Error as IoError, ErrorKind as IoErrorKind, Write};
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant, SystemTime};

/// For each address we're connected to, a period of this duration increases the score by 1.
const CONNEC_DURATION_PER_SCORE: Duration = Duration::from_secs(10);
/// Maximum value for the score.
const MAX_SCORE: u32 = 100;
/// Initial score that a node discovered through Kademlia receives.
const KADEMLIA_DISCOVERY_INITIAL_SCORE: u32 = 10;
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

// TODO: should be merged with the Kademlia k-buckets

/// Stores information about the topology of the network.
#[derive(Debug)]
pub struct NetTopology {
	store: FnvHashMap<PeerId, PeerInfo>,
	cache_path: Option<PathBuf>,
}

impl Default for NetTopology {
	#[inline]
	fn default() -> NetTopology {
		NetTopology::memory()
	}
}

impl NetTopology {
	/// Initializes a new `NetTopology` that isn't tied to any file.
	///
	/// `flush_to_disk()` will be a no-op.
	#[inline]
	pub fn memory() -> NetTopology {
		NetTopology {
			store: Default::default(),
			cache_path: None,
		}
	}

	/// Builds a `NetTopology` that will use `path` as a cache.
	///
	/// This function tries to load a known topology from the file. If the file doesn't exist
	/// or contains garbage data, the execution still continues.
	///
	/// Calling `flush_to_disk()` in the future writes to the given path.
	pub fn from_file<P: AsRef<Path>>(path: P) -> NetTopology {
		let path = path.as_ref();
		debug!(target: "sub-libp2p", "Initializing peer store for JSON file {:?}", path);
		NetTopology {
			store: try_load(path),
			cache_path: Some(path.to_owned()),
		}
	}

	/// Writes the topology into the path passed to `from_file`.
	///
	/// No-op if the object was created with `memory()`.
	pub fn flush_to_disk(&self) -> Result<(), IoError> {
		let path = match self.cache_path {
			Some(ref p) => p,
			None => return Ok(())
		};

		let file = fs::File::create(path)?;
		serialize(file, &self.store)
	}

	/// Perform a cleanup pass, removing all obsolete addresses and peers.
	///
	/// This should be done from time to time.
	pub fn cleanup(&mut self) {
		let now_systime = SystemTime::now();
		self.store.retain(|_, peer| {
			peer.addrs.retain(|a| {
				a.expires > now_systime
			});
			!peer.addrs.is_empty()
		});
	}

	/// Returns a list of all the known peers.
	pub fn peers(&self) -> impl Iterator<Item = &PeerId> {
		self.store.keys()
	}

	/// Returns the known potential addresses of a peer, ordered by score.
	///
	/// If we're already connected to that peer, the address(es) we're connected with will be at
	/// the top of the list.
	// TODO: filter out backed off ones?
	pub fn addrs_of_peer(&self, peer: &PeerId) -> impl Iterator<Item = &Multiaddr> {
		let peer = if let Some(peer) = self.store.get(peer) {
			peer
		} else {
			// TODO: use an EitherIterator or something
			return Vec::new().into_iter();
		};

		let now = SystemTime::now();
		let mut list = peer.addrs.iter().filter_map(move |addr| {
			let (score, connected) = addr.score_and_is_connected();
			if (addr.expires >= now && score > 0) || connected {
				Some((score, &addr.addr))
			} else {
				None
			}
		}).collect::<Vec<_>>();
		list.sort_by(|a, b| a.0.cmp(&b.0));
		// TODO: meh, optimize
		let l = list.into_iter().map(|(_, addr)| addr).collect::<Vec<_>>();
		l.into_iter()
	}

	/// Returns a list of all the known addresses of peers, ordered by the
	/// order in which we should attempt to connect to them.
	///
	/// Because of expiration and back-off mechanisms, this list can grow
	/// by itself over time. The `Instant` that is returned corresponds to
	/// the earlier known time when a new entry will be added automatically to
	/// the list.
	pub fn addrs_to_attempt(&self) -> (impl Iterator<Item = (&PeerId, &Multiaddr)>, Instant) {
		// TODO: optimize
		let now = Instant::now();
		let now_systime = SystemTime::now();
		let mut instant = now + Duration::from_secs(3600);
		let mut addrs_out = Vec::new();

		for (peer, info) in &self.store {
			for addr in &info.addrs {
				let (score, is_connected) = addr.score_and_is_connected();
				if score == 0 || addr.expires < now_systime {
					continue;
				}
				if !is_connected && addr.back_off_until > now {
					instant = cmp::min(instant, addr.back_off_until);
					continue;
				}

				addrs_out.push(((peer, &addr.addr), score));
			}
		}

		addrs_out.sort_by(|a, b| b.1.cmp(&a.1));
		(addrs_out.into_iter().map(|a| a.0), instant)
	}

	/// Adds an address corresponding to a boostrap node.
	///
	/// We assume that the address is valid, so its score starts very high.
	pub fn add_bootstrap_addr(&mut self, peer: &PeerId, addr: Multiaddr) {
		let now_systime = SystemTime::now();
		let now = Instant::now();

		let peer = peer_access(&mut self.store, peer);

		let mut found = false;
		peer.addrs.retain(|a| {
			if a.expires < now_systime {
				return false;
			}
			if a.addr == addr {
				found = true;
			}
			true
		});

		if !found {
			peer.addrs.push(Addr {
				addr,
				expires: now_systime + BOOTSTRAP_NODE_EXPIRATION,
				back_off_until: now,
				next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
				score: Mutex::new(AddrScore {
					connected_since: None,
					score: BOOTSTRAP_NODE_SCORE,
					latest_score_update: now,
				}),
			});
		}
	}

	/// Adds an address discovered through the Kademlia DHT.
	///
	/// This address is not necessarily valid and should expire after a TTL.
	pub fn add_kademlia_discovered_addr(&mut self, peer_id: &PeerId, addr: Multiaddr) {
		let now_systime = SystemTime::now();
		let now = Instant::now();

		let peer = peer_access(&mut self.store, peer_id);

		let mut found = false;
		peer.addrs.retain(|a| {
			if a.expires < now_systime {
				return false;
			}
			if a.addr == addr {
				found = true;
			}
			true
		});

		if !found {
			trace!(target: "sub-libp2p", "Peer store: adding address {} for {:?}", addr, peer_id);
			peer.addrs.push(Addr {
				addr,
				expires: now_systime + KADEMLIA_DISCOVERY_EXPIRATION,
				back_off_until: now,
				next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
				score: Mutex::new(AddrScore {
					connected_since: None,
					score: KADEMLIA_DISCOVERY_INITIAL_SCORE,
					latest_score_update: now,
				}),
			});
		}
	}

	/// Indicates the peer store that we're connected to this given address.
	///
	/// This increases the score of the address that we connected to. Since we assume that only
	/// one peer can be reached with any specific address, we also remove all addresses from other
	/// peers that match the one we connected to.
	pub fn report_connected(&mut self, addr: &Multiaddr, peer: &PeerId) {
		let now = Instant::now();

		// Just making sure that we have an entry for this peer in `store`, but don't use it.
		let _ = peer_access(&mut self.store, peer);

		for (peer_in_store, info_in_store) in self.store.iter_mut() {
			if peer == peer_in_store {
				if let Some(addr) = info_in_store.addrs.iter_mut().find(|a| &a.addr == addr) {
					addr.connected_now();
					addr.back_off_until = now;
					addr.next_back_off = FIRST_CONNECT_FAIL_BACKOFF;
					continue;
				}

				// TODO: a else block would be better, but we get borrowck errors
				info_in_store.addrs.push(Addr {
					addr: addr.clone(),
					expires: SystemTime::now() + EXPIRATION_PUSH_BACK_CONNEC,
					back_off_until: now,
					next_back_off: FIRST_CONNECT_FAIL_BACKOFF,
					score: Mutex::new(AddrScore {
						connected_since: Some(now),
						latest_score_update: now,
						score: KADEMLIA_DISCOVERY_INITIAL_SCORE
					}),
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

	/// Indicates the peer store that we're disconnected from an address.
	///
	/// There's no need to indicate a peer ID, as each address can only have one peer ID.
	/// If we were indeed connected to this addr, then we can find out which peer ID it is.
	pub fn report_disconnected(&mut self, addr: &Multiaddr, reason: DisconnectReason) {
		let score_diff = match reason {
			DisconnectReason::ClosedGracefully => -1,
		};

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
					return;
				}
			}
		}
	}

	/// Indicates the peer store that we failed to connect to an address.
	///
	/// We don't care about which peer is supposed to be behind that address. If we failed to dial
	/// it for a specific peer, we would also fail to dial it for all peers that have this
	/// address.
	pub fn report_failed_to_connect(&mut self, addr: &Multiaddr) {
		for info in self.store.values_mut() {
			for a in info.addrs.iter_mut() {
				if &a.addr == addr {
					a.adjust_score(SCORE_DIFF_ON_FAILED_TO_CONNECT);
					a.back_off_until = Instant::now() + a.next_back_off;
					a.next_back_off = cmp::min(a.next_back_off * FAIL_BACKOFF_MULTIPLIER, MAX_BACKOFF);
				}
			}
		}
	}
}

/// Reason why we disconnected from a peer.
pub enum DisconnectReason {
	/// The disconnection was graceful.
	ClosedGracefully,
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
	score: Mutex<AddrScore>,
}

impl Clone for Addr {
	fn clone(&self) -> Addr {
		Addr {
			addr: self.addr.clone(),
			expires: self.expires.clone(),
			next_back_off: self.next_back_off.clone(),
			back_off_until: self.back_off_until.clone(),
			score: Mutex::new(self.score.lock().clone()),
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
	/// Sets the addr to connected.
	fn connected_now(&self) {
		let mut score = self.score.lock();
		let now = Instant::now();
		Addr::flush(&mut score, now);
		score.connected_since = Some(now);
	}

	/// Applies a modification to the score.
	fn adjust_score(&self, score_diff: i32) {
		let mut score = self.score.lock();
		Addr::flush(&mut score, Instant::now());
		if score_diff >= 0 {
			score.score = cmp::min(MAX_SCORE, score.score + score_diff as u32);
		} else {
			score.score = score.score.saturating_sub(-score_diff as u32);
		}
	}

	/// Sets the addr to disconnected and applies a modification to the score.
	fn disconnected_now(&self, score_diff: i32) {
		let mut score = self.score.lock();
		Addr::flush(&mut score, Instant::now());
		score.connected_since = None;
		if score_diff >= 0 {
			score.score = cmp::min(MAX_SCORE, score.score + score_diff as u32);
		} else {
			score.score = score.score.saturating_sub(-score_diff as u32);
		}
	}

	/// Returns the score, and true if we are connected to this addr.
	fn score_and_is_connected(&self) -> (u32, bool) {
		let mut score = self.score.lock();
		Addr::flush(&mut score, Instant::now());
		let is_connected = score.connected_since.is_some();
		(score.score, is_connected)
	}

	/// Updates `score` and `latest_score_update`, and returns the score.
	fn score(&self) -> u32 {
		let mut score = self.score.lock();
		Addr::flush(&mut score, Instant::now());
		score.score
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
	let a_ms = a.as_secs() * 1_000_000 + (a.subsec_nanos() / 1_000) as u64;
	let b_ms = b.as_secs() * 1_000_000 + (b.subsec_nanos() / 1_000) as u64;
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

impl<'a> From<&'a Addr> for SerializedAddr {
	fn from(addr: &'a Addr) -> SerializedAddr {
		SerializedAddr {
			addr: addr.addr.to_string(),
			expires: addr.expires,
			score: addr.score(),
		}
	}
}

/// Attempts to load storage from a file.
/// Deletes the file and returns an empty map if the file doesn't exist, cannot be opened
/// or is corrupted.
fn try_load(path: impl AsRef<Path>) -> FnvHashMap<PeerId, PeerInfo> {
	let path = path.as_ref();
	if !path.exists() {
		debug!(target: "sub-libp2p", "Peer storage file {:?} doesn't exist", path);
		return Default::default()
	}

	let mut file = match fs::File::open(path) {
		Ok(f) => f,
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
			Ok(serde_json::Value::Object(map)) => deserialize_tolerant(map.into_iter()),
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
/// Skips entries that are invalid.
fn deserialize_tolerant(
	iter: impl Iterator<Item = (String, serde_json::Value)>
) -> FnvHashMap<PeerId, PeerInfo> {
	let now = Instant::now();
	let now_systime = SystemTime::now();

	let mut out = FnvHashMap::default();
	for (peer, info) in iter {
		let peer: PeerId = match peer.parse() {
			Ok(p) => p,
			Err(_) => continue,
		};

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
				score: Mutex::new(AddrScore {
					connected_since: None,
					score: addr.score,
					latest_score_update: now,
				}),
			});
		}

		if addrs.is_empty() {
			continue;
		}

		out.insert(peer, PeerInfo { addrs });
	}

	out
}

/// Attempts to turn a deserialized version of the storage into the final version.
///
/// Skips entries that are invalid or expired.
fn serialize<W: Write>(out: W, map: &FnvHashMap<PeerId, PeerInfo>) -> Result<(), IoError> {
	let now = SystemTime::now();
	let array: FnvHashMap<_, _> = map.iter().filter_map(|(peer, info)| {
		if info.addrs.is_empty() {
			return None
		}

		let peer = peer.to_base58();
		let info = SerializedPeerInfo {
			addrs: info.addrs.iter()
				.filter(|a| a.expires > now)
				.map(Into::into)
				.collect(),
		};

		Some((peer, info))
	}).collect();

	serde_json::to_writer_pretty(out, &array)
		.map_err(|err| IoError::new(IoErrorKind::Other, err))
}
