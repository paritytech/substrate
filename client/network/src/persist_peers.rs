// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

use std::{
	collections::{HashMap, HashSet},
	fmt,
	future::Future,
	io,
	path::{Path, PathBuf},
	pin::Pin,
	task::{Context, Poll},
	time::{Duration, Instant},
};

use futures::FutureExt;
use lru::LruCache;

use sc_peerset::PeersetHandle;

use crate::{utils, Multiaddr, PeerId};

type BoxedFuture<T> = Pin<Box<dyn Future<Output = T> + Send + 'static>>;
type Never = std::convert::Infallible;
type ProtocolType = String;

const FLUSH_INTERVAL: Duration = Duration::from_secs(5);
const PEER_ADDRS_CACHE_SIZE: usize = 100;

const PEER_ADDRS_FILENAME: &str = "peer-addrs.json";
const PEER_SETS_FILENAME: &str = "peer-sets.json";

pub struct PersistPeerAddrs {
	storage_dir: PathBuf,
	flushed_at: Instant,
	protocols: HashMap<ProtocolType, LruCache<PeerId, HashSet<Multiaddr>>>,
	busy: Option<BoxedFuture<Result<(), io::Error>>>,
}

impl PersistPeerAddrs {
	pub fn load(storage_dir: PathBuf) -> Self {
		let load_from_file = storage_dir.join(PEER_ADDRS_FILENAME);

		let protocols = match persist_peer_addrs::load(&load_from_file) {
			Ok(restored) => restored,
			Err(reason) => {
				log::warn!("Failed to load peer addresses: {:?}", reason);
				Default::default()
			},
		};

		let protocols = protocols
			.into_iter()
			.map(|(protocol, entries)| {
				let cache = entries.into_iter().rev().fold(
					LruCache::new(PEER_ADDRS_CACHE_SIZE),
					|mut acc, persist_peer_addrs::PeerEntry { peer_id, addrs }| {
						if let Ok(peer_id) = peer_id.parse() {
							acc.push(peer_id, addrs.into_iter().collect::<HashSet<_>>());
						}
						acc
					},
				);
				(protocol, cache)
			})
			.collect();

		Self { storage_dir, flushed_at: Instant::now(), protocols, busy: None }
	}

	pub fn report_peer_addr(
		&mut self,
		peer_id: &PeerId,
		protocol: impl AsRef<[u8]>,
		addr: &Multiaddr,
	) {
		let protocol = String::from_utf8(protocol.as_ref().to_owned()).expect(
			"According to the `crate::discovery::protocol_name_from_protocol_id` \
					and `<ProtocolId as AsRef<str>>` it's a correct UTF-8 string",
		);

		let entries = self
			.protocols
			.entry(protocol)
			.or_insert_with(|| LruCache::new(PEER_ADDRS_CACHE_SIZE));
		if let Some(peer_addrs) = entries.get_mut(peer_id) {
			peer_addrs.insert(addr.to_owned());
		} else {
			entries.push(peer_id.to_owned(), [addr.to_owned()].into_iter().collect());
		}
	}

	pub fn peer_addrs<'a>(
		&'a mut self,
		peer_id: &'a PeerId,
		protocols: impl IntoIterator<Item = impl AsRef<[u8]> + 'a>,
	) -> impl Iterator<Item = &'a Multiaddr> {
		let protocols = protocols.into_iter().collect::<Vec<_>>();

		self.protocols
			.iter_mut()
			.filter_map(move |(protocol, entries)| {
				if protocols.iter().any(|p| p.as_ref() == protocol.as_bytes()) {
					Some(entries)
				} else {
					None
				}
			})
			.flat_map(|entries| entries.get(peer_id).into_iter())
			.flat_map(IntoIterator::into_iter)
	}

	pub fn poll(&mut self, cx: &mut Context) -> Poll<Never> {
		if let Some(busy_future) = self.busy.as_mut() {
			if let Poll::Ready(result) = busy_future.poll_unpin(cx) {
				self.busy = None;
				self.flushed_at = Instant::now();

				if let Err(reason) = result {
					log::warn!("Failed to persist peer addresses: {}", reason);
				}
			}
		} else if self.flushed_at.elapsed() > FLUSH_INTERVAL {
			let entries = self
				.protocols
				.iter()
				.map(|(protocol, entries)| {
					let entries = entries
						.iter()
						.map(|(peer_id, addrs)| {
							let peer_id = peer_id.to_base58();
							let addrs = addrs.into_iter().cloned().collect();

							persist_peer_addrs::PeerEntry { peer_id, addrs }
						})
						.collect::<Vec<_>>();
					(protocol.to_owned(), entries)
				})
				.collect();

			let busy_future =
				persist_peer_addrs::persist(self.storage_dir.to_owned(), entries).boxed();
			self.busy = Some(busy_future);
		}
		Poll::Pending
	}
}

mod persist_peer_addrs {
	use super::*;

	#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
	pub(super) struct PeerEntry {
		pub peer_id: String,
		pub addrs: Vec<Multiaddr>,
	}

	pub(super) async fn persist(
		storage_dir: PathBuf,
		protocols: HashMap<ProtocolType, Vec<PeerEntry>>,
	) -> Result<(), io::Error> {
		let persist_to_file = storage_dir.join(PEER_ADDRS_FILENAME);
		utils::json_file::save(&persist_to_file, &protocols).await?;

		Ok(())
	}

	pub(super) fn load(path: &Path) -> Result<HashMap<ProtocolType, Vec<PeerEntry>>, io::Error> {
		let entries = utils::json_file::load_sync(path)?.unwrap_or_default();
		Ok(entries)
	}
}

pub struct PersistPeersets(BoxedFuture<Never>);
pub use peersets::load as peersets_load;

impl PersistPeersets {
	pub fn new(storage_dir: PathBuf, peerset_handle: PeersetHandle) -> Self {
		let busy_future = async move {
			let mut ticks = tokio::time::interval(FLUSH_INTERVAL);
			ticks.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

			loop {
				let _ = ticks.tick().await;
				if let Err(reason) = peersets::persist(&storage_dir, &peerset_handle).await {
					log::warn!("Error persisting peer sets: {}", reason);
				}
			}
		};
		Self(busy_future.boxed())
	}

	pub fn poll(&mut self, cx: &mut Context) -> Poll<Never> {
		self.0.poll_unpin(cx)
	}
}

mod peersets {
	use super::*;

	#[derive(Debug, serde::Serialize, serde::Deserialize)]
	pub(crate) struct PeerInfo {
		pub peer_id: String,
		pub sets: Vec<usize>,
	}

	pub(super) async fn persist(
		storage_dir: &Path,
		peerset_handle: &PeersetHandle,
	) -> Result<(), io::Error> {
		let persist_to_file = storage_dir.join(PEER_SETS_FILENAME);

		let peersets_dumped = peerset_handle
			.dump_state()
			.await
			.map_err(|()| io::Error::new(io::ErrorKind::BrokenPipe, "oneshot channel failure"))?
			.into_iter()
			.map(|(peer_id, sets)| PeerInfo { peer_id: peer_id.to_base58(), sets })
			.collect::<Vec<_>>();

		utils::json_file::save(&persist_to_file, &peersets_dumped).await?;
		Ok(())
	}

	pub fn load(dir: impl AsRef<Path>) -> Result<Vec<(PeerId, Vec<usize>)>, io::Error> {
		let path = dir.as_ref().join("peer-sets.json");

		let entries: Vec<PeerInfo> = utils::json_file::load_sync(&path)?.unwrap_or_default();
		Ok(entries
			.into_iter()
			.filter_map(|peer_info| {
				if let Ok(peer_id) = peer_info.peer_id.parse::<PeerId>() {
					Some((peer_id, peer_info.sets))
				} else {
					None
				}
			})
			.collect())
	}

	impl fmt::Debug for PersistPeersets {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			f.debug_struct("PersistPeersets").finish()
		}
	}
}
