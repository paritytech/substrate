// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Handling of blobs that may be compressed, based on an 8-byte magic identifier
//! at the head.

use std::{
	borrow::Cow,
	io::{Read, Write},
};

// An arbitrary prefix, that indicates a blob beginning with should be decompressed with
// Zstd compression.
//
// This differs from the WASM magic bytes, so real WASM blobs will not have this prefix.
const ZSTD_PREFIX: [u8; 8] = [82, 188, 83, 118, 70, 219, 142, 5];

/// A recommendation for the bomb limit for code blobs.
///
/// This may be adjusted upwards in the future, but is set much higher than the
/// expected maximum code size. When adjusting upwards, nodes should be updated
/// before performing a runtime upgrade to a blob with larger compressed size.
pub const CODE_BLOB_BOMB_LIMIT: usize = 50 * 1024 * 1024;

/// A possible bomb was encountered.
#[derive(Debug, Clone, PartialEq, thiserror::Error)]
pub enum Error {
	/// Decoded size was too large, and the code payload may be a bomb.
	#[error("Possible compression bomb encountered")]
	PossibleBomb,
	/// The compressed value had an invalid format.
	#[error("Blob had invalid format")]
	Invalid,
}

fn read_from_decoder(
	decoder: impl Read,
	blob_len: usize,
	bomb_limit: usize,
) -> Result<Vec<u8>, Error> {
	let mut decoder = decoder.take((bomb_limit + 1) as u64);

	let mut buf = Vec::with_capacity(blob_len);
	decoder.read_to_end(&mut buf).map_err(|_| Error::Invalid)?;

	if buf.len() <= bomb_limit {
		Ok(buf)
	} else {
		Err(Error::PossibleBomb)
	}
}

fn decompress_zstd(blob: &[u8], bomb_limit: usize) -> Result<Vec<u8>, Error> {
	let decoder = zstd::Decoder::new(blob).map_err(|_| Error::Invalid)?;

	read_from_decoder(decoder, blob.len(), bomb_limit)
}

/// Decode a blob, if it indicates that it is compressed. Provide a `bomb_limit`, which
/// is the limit of bytes which should be decompressed from the blob.
pub fn decompress(blob: &[u8], bomb_limit: usize) -> Result<Cow<[u8]>, Error> {
	if blob.starts_with(&ZSTD_PREFIX) {
		decompress_zstd(&blob[ZSTD_PREFIX.len()..], bomb_limit).map(Into::into)
	} else {
		Ok(blob.into())
	}
}

/// Encode a blob as compressed. If the blob's size is over the bomb limit,
/// this will not compress the blob, as the decoder will not be able to be
/// able to differentiate it from a compression bomb.
pub fn compress(blob: &[u8], bomb_limit: usize) -> Option<Vec<u8>> {
	if blob.len() > bomb_limit {
		return None
	}

	let mut buf = ZSTD_PREFIX.to_vec();

	{
		let mut v = zstd::Encoder::new(&mut buf, 3).ok()?.auto_finish();
		v.write_all(blob).ok()?;
	}

	Some(buf)
}

#[cfg(test)]
mod tests {
	use super::*;

	const BOMB_LIMIT: usize = 10;

	#[test]
	fn refuse_to_encode_over_limit() {
		let mut v = vec![0; BOMB_LIMIT + 1];
		assert!(compress(&v, BOMB_LIMIT).is_none());

		let _ = v.pop();
		assert!(compress(&v, BOMB_LIMIT).is_some());
	}

	#[test]
	fn compress_and_decompress() {
		let v = vec![0; BOMB_LIMIT];

		let compressed = compress(&v, BOMB_LIMIT).unwrap();

		assert!(compressed.starts_with(&ZSTD_PREFIX));
		assert_eq!(&decompress(&compressed, BOMB_LIMIT).unwrap()[..], &v[..])
	}

	#[test]
	fn decompresses_only_when_magic() {
		let v = vec![0; BOMB_LIMIT + 1];

		assert_eq!(&decompress(&v, BOMB_LIMIT).unwrap()[..], &v[..]);
	}

	#[test]
	fn possible_bomb_fails() {
		let encoded_bigger_than_bomb = vec![0; BOMB_LIMIT + 1];
		let mut buf = ZSTD_PREFIX.to_vec();

		{
			let mut v = zstd::Encoder::new(&mut buf, 3).unwrap().auto_finish();
			v.write_all(&encoded_bigger_than_bomb[..]).unwrap();
		}

		assert_eq!(decompress(&buf[..], BOMB_LIMIT).err(), Some(Error::PossibleBomb));
	}
}
