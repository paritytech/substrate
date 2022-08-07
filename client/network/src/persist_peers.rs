use std::{
	collections::HashSet,
	fmt,
	future::Future,
	io,
	path::{Path, PathBuf},
	pin::Pin,
	sync::Arc,
	task::{Context, Poll},
	time::{Duration, Instant},
};

use futures::FutureExt;
use lru::LruCache;

use sc_peerset::PeersetHandle;

use crate::{Multiaddr, PeerId};

type BoxedFuture<T> = Pin<Box<dyn Future<Output = T> + Send + 'static>>;
type Never = std::convert::Infallible;

const FLUSH_INTERVAL: Duration = Duration::from_secs(5);
const PEER_ADDRS_CACHE_SIZE: usize = 100;

pub struct PersistPeerAddrs {
	paths: Arc<Paths>,
	flushed_at: Instant,
	entries: LruCache<PeerId, HashSet<Multiaddr>>,
	busy: Option<BoxedFuture<Result<(), io::Error>>>,
}

impl PersistPeerAddrs {
	pub fn load(dir: impl AsRef<Path>) -> Self {
		let paths = Paths::new(dir, "peer-addrs");

		let entries = match persist_peer_addrs::load(&paths.path) {
			Ok(restored) => restored,
			Err(reason) => {
				log::warn!("Failed to load peer addresses: {:?}", reason);
				vec![]
			},
		};

		let entries = entries.into_iter().rev().fold(
			LruCache::new(PEER_ADDRS_CACHE_SIZE),
			|mut acc, persist_peer_addrs::PeerEntry { peer_id, addrs }| {
				if let Ok(peer_id) = peer_id.parse() {
					acc.push(peer_id, addrs.into_iter().collect::<HashSet<_>>());
				}
				acc
			},
		);

		Self { paths: Arc::new(paths), flushed_at: Instant::now(), entries, busy: None }
	}

	pub fn report_peer_addr(&mut self, peer_id: &PeerId, addr: &Multiaddr) {
		if let Some(peer_addrs) = self.entries.get_mut(peer_id) {
			peer_addrs.insert(addr.to_owned());
		} else {
			self.entries.push(peer_id.to_owned(), [addr.to_owned()].into_iter().collect());
		}
	}

	pub fn peer_addrs(&mut self, peer_id: &PeerId) -> impl Iterator<Item = &Multiaddr> {
		self.entries.get(peer_id).map(IntoIterator::into_iter).into_iter().flatten()
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
				.entries
				.iter()
				.map(|(peer_id, addrs)| {
					let peer_id = peer_id.to_base58();
					let addrs = addrs.into_iter().cloned().collect();

					persist_peer_addrs::PeerEntry { peer_id, addrs }
				})
				.collect::<Vec<_>>();

			let busy_future = persist_peer_addrs::persist(Arc::clone(&self.paths), entries).boxed();
			self.busy = Some(busy_future);
		}
		Poll::Pending
	}
}

mod persist_peer_addrs {
	use super::*;
	use tokio::io::AsyncWriteExt;

	#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
	pub(super) struct PeerEntry {
		pub peer_id: String,
		pub addrs: Vec<Multiaddr>,
	}

	pub(super) async fn persist(
		paths: Arc<Paths>,
		entries: Vec<PeerEntry>,
	) -> Result<(), io::Error> {
		let mut tmp_file = tokio::fs::OpenOptions::new()
			.create(true)
			.write(true)
			.open(&paths.tmp_path)
			.await?;
		let serialized = serde_json::to_vec_pretty(&entries)?;

		tmp_file.write_all(&serialized).await?;
		tmp_file.flush().await?;
		std::mem::drop(tmp_file);

		tokio::fs::rename(&paths.tmp_path, &paths.path).await?;

		Ok(())
	}

	pub(super) fn load(path: impl AsRef<Path>) -> Result<Vec<PeerEntry>, io::Error> {
		let file = match std::fs::OpenOptions::new().read(true).open(path.as_ref()) {
			Ok(file) => file,
			Err(not_found) if not_found.kind() == std::io::ErrorKind::NotFound =>
				return Ok(Vec::new()),
			Err(reason) => return Err(reason),
		};
		let entries = serde_json::from_reader(file)?;
		Ok(entries)
	}
}

pub struct PersistPeersets(BoxedFuture<Never>);
pub use peersets::load as peersets_load;

impl PersistPeersets {
	pub fn new(dir: impl AsRef<Path>, peerset_handle: PeersetHandle) -> Self {
		let paths = Paths::new(dir, "peer-sets");
		let busy_future = async move {
			let mut ticks = tokio::time::interval(FLUSH_INTERVAL);
			ticks.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

			loop {
				let _ = ticks.tick().await;
				if let Err(reason) = peersets::persist(&paths, &peerset_handle).await {
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
	pub struct PeerInfo {
		pub peer_id: String,
		pub reputation: i32,
		pub sets: Vec<usize>,
	}

	pub(super) async fn persist(
		paths: &Paths,
		peerset_handle: &PeersetHandle,
	) -> Result<(), io::Error> {
		use tokio::io::AsyncWriteExt;

		let peersets_dumped = peerset_handle
			.dump_state()
			.await
			.map_err(|()| io::Error::new(io::ErrorKind::BrokenPipe, "oneshot channel failure"))?
			.into_iter()
			.map(|(peer_id, reputation, sets)| PeerInfo {
				peer_id: peer_id.to_base58(),
				reputation,
				sets,
			})
			.collect::<Vec<_>>();

		let mut tmp_file = tokio::fs::OpenOptions::new()
			.create(true)
			.write(true)
			.open(&paths.tmp_path)
			.await?;
		let serialized = serde_json::to_vec_pretty(&peersets_dumped)?;
		tmp_file.write_all(&serialized).await?;
		tmp_file.flush().await?;
		std::mem::drop(tmp_file);

		tokio::fs::rename(&paths.tmp_path, &paths.path).await?;

		Ok(())
	}

	pub fn load(dir: impl AsRef<Path>) -> Result<Vec<(PeerId, i32, Vec<usize>)>, io::Error> {
		let mut path = dir.as_ref().to_owned();
		path.push("peer-sets.json");

		match std::fs::OpenOptions::new().read(true).open(&path) {
			Ok(f) => {
				let peersets: Vec<PeerInfo> = serde_json::from_reader(f)?;

				Ok(peersets
					.into_iter()
					.filter_map(|peer_info| {
						if let Ok(peer_id) = peer_info.peer_id.parse::<PeerId>() {
							Some((peer_id, peer_info.reputation, peer_info.sets))
						} else {
							None
						}
					})
					.collect())
			},
			Err(not_found) if not_found.kind() == io::ErrorKind::NotFound => Ok(vec![]),
			Err(reason) => Err(reason),
		}
	}

	impl fmt::Debug for PersistPeersets {
		fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
			f.debug_struct("PersistPeersets").finish()
		}
	}
}

#[derive(Debug)]
struct Paths {
	path: PathBuf,
	tmp_path: PathBuf,
}

impl Paths {
	pub fn new(net_config_path: impl AsRef<Path>, name: impl AsRef<str>) -> Self {
		let mut p = net_config_path.as_ref().to_owned();
		p.push(name.as_ref());

		let path = p.with_extension("json");
		let tmp_path = p.with_extension("tmp");

		Self { path, tmp_path }
	}
}

#[test]
fn test_paths() {
	let p = Paths::new("/tmp", "test");
	assert_eq!(p.path.to_str(), Some("/tmp/test.json"));
	assert_eq!(p.tmp_path.to_str(), Some("/tmp/test.tmp"));
}
