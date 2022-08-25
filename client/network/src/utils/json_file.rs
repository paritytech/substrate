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
