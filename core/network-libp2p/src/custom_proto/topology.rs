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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.?

use libp2p::{core::swarm::ConnectedPoint, Multiaddr, PeerId};
use log::{debug, warn};
use substrate_network_peerset::NetTopology as InnerNetTopology;
use std::fs;
use std::io::{Error as IoError, BufWriter};
use std::path::{Path, PathBuf};
use std::time::Instant;

/// Stores information about the topology of the network.
#[derive(Debug)]
pub struct NetTopology {
	/// The actual storage.
	inner: InnerNetTopology,
	/// Optional path to the file that caches the serialized version of `store`.
	cache_path: Option<PathBuf>,
}

impl NetTopology {
	/// Initializes a new `NetTopology` that isn't tied to any file.
	///
	/// `flush_to_disk()` will be a no-op.
	#[inline]
	pub fn memory(local_peer_id: PeerId) -> NetTopology {
		NetTopology {
			inner: InnerNetTopology::empty(local_peer_id),
			cache_path: None,
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

		if !path.exists() {
			return NetTopology {
				inner: InnerNetTopology::empty(local_peer_id),
				cache_path: Some(path.to_owned()),
			}
		}

		let inner = match fs::File::open(path).and_then(|file| InnerNetTopology::try_load(file, local_peer_id.clone())) {
			Ok(inner) => inner,
			Err(err) => {
				warn!(target: "sub-libp2p", "Failed to load existing peer store: {:?}", err);
				InnerNetTopology::empty(local_peer_id)
			}
		};

		NetTopology {
			inner,
			cache_path: Some(path.to_owned()),
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
		self.inner.serialize(BufWriter::with_capacity(1024 * 1024, file))
	}

	/// Returns the number of peers in the topology, excluding the local peer.
	#[inline]
	pub fn num_peers(&self) -> usize {
		self.inner.num_peers()
	}

	/// Perform a cleanup pass, removing all obsolete addresses and peers.
	///
	/// This should be done from time to time.
	pub fn cleanup(&mut self) {
		self.inner.cleanup();
	}

	/// Returns a list of all the known addresses of peers, ordered by the
	/// order in which we should attempt to connect to them.
	///
	/// Because of expiration and back-off mechanisms, this list can grow
	/// by itself over time. The `Instant` that is returned corresponds to
	/// the earlier known time when a new entry will be added automatically to
	/// the list.
	pub fn addrs_to_attempt(&mut self) -> (impl Iterator<Item = (&PeerId, &Multiaddr)>, Instant) {
		self.inner.addrs_to_attempt()
	}

	/// Adds an address corresponding to a boostrap node.
	///
	/// We assume that the address is valid, so its score starts very high.
	pub fn add_bootstrap_addr(&mut self, peer: &PeerId, addr: Multiaddr) {
		self.inner.add_bootstrap_addr(peer, addr)
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
		self.inner.add_discovered_addrs(peer_id, addrs)
	}

	/// Returns the list of peers that are stored in the topology.
	#[inline]
	pub fn known_peers(&self) -> impl Iterator<Item = &PeerId> {
		self.inner.known_peers()
	}

	/// Returns the addresses stored for a specific peer, and their reputation score.
	///
	/// If `include_expired` is true, includes expired addresses that shouldn't be taken into
	/// account when dialing.
	#[inline]
	pub fn addresses_of_peer(&mut self, peer: &PeerId, include_expired: bool)
		-> impl Iterator<Item = (&Multiaddr, u32)> {
		self.inner.addresses_of_peer(peer, include_expired)
	}

	/// Marks the given peer as connected through the given endpoint.
	pub fn set_connected(&mut self, peer: &PeerId, endpoint: &ConnectedPoint) {
		self.inner.set_connected(peer, endpoint)
	}

	/// Marks the given peer as disconnected. The endpoint is the one we were connected to.
	pub fn set_disconnected(&mut self, peer_id: &PeerId, endpoint: &ConnectedPoint) {
		self.inner.set_disconnected(peer_id, endpoint)
	}

	/// Indicates to the topology that we failed to reach a node when dialing the given address.
	pub fn set_unreachable(&mut self, addr: &Multiaddr) {
		self.inner.set_unreachable(addr)
	}
}
