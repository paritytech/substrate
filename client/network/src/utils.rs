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

use futures::{stream::unfold, FutureExt, Stream, StreamExt};
use futures_timer::Delay;
use linked_hash_set::LinkedHashSet;
use std::{hash::Hash, num::NonZeroUsize, time::Duration};

/// Creates a stream that returns a new value every `duration`.
pub fn interval(duration: Duration) -> impl Stream<Item = ()> + Unpin {
	unfold((), move |_| Delay::new(duration).map(|_| Some(((), ())))).map(drop)
}

/// Wrapper around `LinkedHashSet` with bounded growth.
///
/// In the limit, for each element inserted the oldest existing element will be removed.
#[derive(Debug, Clone)]
pub struct LruHashSet<T: Hash + Eq> {
	set: LinkedHashSet<T>,
	limit: NonZeroUsize,
}

impl<T: Hash + Eq> LruHashSet<T> {
	/// Create a new `LruHashSet` with the given (exclusive) limit.
	pub fn new(limit: NonZeroUsize) -> Self {
		Self { set: LinkedHashSet::new(), limit }
	}

	/// Insert element into the set.
	///
	/// Returns `true` if this is a new element to the set, `false` otherwise.
	/// Maintains the limit of the set by removing the oldest entry if necessary.
	/// Inserting the same element will update its LRU position.
	pub fn insert(&mut self, e: T) -> bool {
		if self.set.insert(e) {
			if self.set.len() == usize::from(self.limit) {
				self.set.pop_front(); // remove oldest entry
			}
			return true
		}
		false
	}
}
pub(crate) mod json_file {
	use serde::{de::DeserializeOwned, Serialize};
	use std::{io::Error as IoError, path::Path};
	use tokio::io::AsyncWriteExt;

	pub(crate) async fn save(
		target_file: impl AsRef<Path>,
		data: &impl Serialize,
	) -> Result<(), IoError> {
		let target_file = target_file.as_ref();
		let tmp_file = target_file.with_extension(EXTENSION_TMP);
		let mut tmp_file_rm_guard = MaybeRmOnDrop::new(&tmp_file);

		let data = serde_json::to_vec_pretty(&data)?;

		let mut temp_fd = tokio::fs::OpenOptions::new()
			.create(true)
			.truncate(true)
			.write(true)
			.open(&tmp_file)
			.await?;

		temp_fd.write_all(&data).await?;
		temp_fd.flush().await?;
		std::mem::drop(temp_fd);

		tokio::fs::rename(&tmp_file, target_file).await?;
		tmp_file_rm_guard.disarm();

		Ok(())
	}

	pub(crate) fn load_sync<D, P>(path: P) -> Result<Option<D>, IoError>
	where
		P: AsRef<Path>,
		D: DeserializeOwned,
	{
		let file = match std::fs::OpenOptions::new().read(true).open(path) {
			Ok(file) => file,
			Err(not_found) if not_found.kind() == std::io::ErrorKind::NotFound => return Ok(None),
			Err(reason) => return Err(reason),
		};
		let entries = serde_json::from_reader(file)?;
		Ok(Some(entries))
	}

	const EXTENSION_TMP: &str = "tmp";

	struct MaybeRmOnDrop<P: AsRef<Path>>(Option<P>);

	impl<P: AsRef<Path>> MaybeRmOnDrop<P> {
		fn new(path: P) -> Self {
			Self(Some(path))
		}
		fn disarm(&mut self) {
			self.0.take();
		}
	}

	impl<P: AsRef<Path>> Drop for MaybeRmOnDrop<P> {
		fn drop(&mut self) {
			if let Some(file) = self.0.take() {
				if let Err(reason) = std::fs::remove_file(file.as_ref()) {
					log::error!("Failed to cleanup temp-file: {:?}: {}", file.as_ref(), reason);
				}
			}
		}
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	fn maintains_limit() {
		let three = NonZeroUsize::new(3).unwrap();
		let mut set = LruHashSet::<u8>::new(three);

		// First element.
		assert!(set.insert(1));
		assert_eq!(vec![&1], set.set.iter().collect::<Vec<_>>());

		// Second element.
		assert!(set.insert(2));
		assert_eq!(vec![&1, &2], set.set.iter().collect::<Vec<_>>());

		// Inserting the same element updates its LRU position.
		assert!(!set.insert(1));
		assert_eq!(vec![&2, &1], set.set.iter().collect::<Vec<_>>());

		// We reached the limit. The next element forces the oldest one out.
		assert!(set.insert(3));
		assert_eq!(vec![&1, &3], set.set.iter().collect::<Vec<_>>());
	}

	#[tokio::test]
	async fn json_data_saved_to_file_and_loaded_from_it() {
		let tmp_dir = tempfile::TempDir::new().expect("Failed to create temp-dir");
		assert!(
			tokio::fs::read_dir(tmp_dir.path())
				.await
				.expect("read_dir(tmp_dir) failed")
				.next_entry()
				.await
				.expect("read_dir(tmp_dir).next_entry() failed")
				.is_none(),
			"temporary dir is not empty at the beginning of the test"
		);

		let data = serde_json::json!({"key": "value"});
		let file = tmp_dir.path().join("data.json");

		json_file::save(&file, &data).await.expect("Failed to save JSON to file");

		let loaded = json_file::load_sync::<serde_json::Value, _>(&file)
			.expect("Failed to load from JSON-file")
			.expect("JSON-file missing");

		assert_eq!(loaded, data);

		tokio::fs::remove_file(&file).await.expect("Failed to remove JSON-file");
		assert!(
			tokio::fs::read_dir(tmp_dir.path())
				.await
				.expect("read_dir(tmp_dir) failed")
				.next_entry()
				.await
				.expect("read_dir(tmp_dir).next_entry() failed")
				.is_none(),
			"temporary dir is not empty at the completion of the test"
		);
	}

	#[tokio::test]
	async fn json_data_cant_be_serialized_but_no_temp_file_left() {
		use std::collections::HashMap;

		let tmp_dir = tempfile::TempDir::new().expect("Failed to create temp-dir");
		assert!(
			tokio::fs::read_dir(tmp_dir.path())
				.await
				.expect("read_dir(tmp_dir) failed")
				.next_entry()
				.await
				.expect("read_dir(tmp_dir).next_entry() failed")
				.is_none(),
			"temporary dir is not empty at the beginning of the test"
		);

		let data = [((), ())].into_iter().collect::<HashMap<(), ()>>();
		let file = tmp_dir.path().join("data.json");

		let should_be_error = json_file::save(&file, &data).await;

		let should_be_invalid_data =
			should_be_error.err().expect("save_to_json_file should have failed");
		assert_eq!(
			should_be_invalid_data.kind(),
			std::io::ErrorKind::InvalidData,
			"save_to_json_file has failed with reason other than serialization failure: {}",
			should_be_invalid_data
		);

		assert!(
			tokio::fs::read_dir(tmp_dir.path())
				.await
				.expect("read_dir(tmp_dir) failed")
				.next_entry()
				.await
				.expect("read_dir(tmp_dir).next_entry() failed")
				.is_none(),
			"temporary dir is not empty at the completion of the test"
		);
	}
}
