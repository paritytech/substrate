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
	let file = match std::fs::File::open(path) {
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

#[cfg(test)]
mod tests {

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

		super::save(&file, &data).await.expect("Failed to save JSON to file");

		let loaded = super::load_sync::<serde_json::Value, _>(&file)
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

		let should_be_error = super::save(&file, &data).await;

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
