// This file is part of Substrate.

// Copyright (C) 2017-2021 Parity Technologies (UK) Ltd.
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

use std::borrow::Cow;
use std::io::Read;

// An arbitrary prefix, that indicates a blob beginning with should be decoded with
// Zstd compression.
const ZSTD_PREFIX: [u8; 8] = [82, 188, 83, 118, 70, 219, 142, 5];

/// The maximum size for compressed blobs.
pub const BOMB_LIMIT: u64 = 50 * 1024 * 1024;

/// A possible bomb was encountered.
#[derive(Debug, Clone, PartialEq)]
pub enum Error {
	/// Decoded size was too large, and the code payload may be a bomb.
	PossibleBomb,
	/// The compressed value had an invalid format.
	Invalid,
}

impl std::fmt::Display for Error {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		match *self {
			Error::PossibleBomb => write!(f, "Possible compression bomb encountered"),
			Error::Invalid => write!(f, "Blob had invalid format"),
		}
	}
}

impl std::error::Error for Error { }

fn read_from_decoder(decoder: impl Read, blob_len: usize) -> Result<Vec<u8>, Error> {
	let mut decoder = decoder.take(BOMB_LIMIT);

	let mut buf = Vec::with_capacity(blob_len);
	decoder.read_to_end(&mut buf).map_err(|_| Error::Invalid)?;

	if (buf.len() as u64) < BOMB_LIMIT {
		Ok(buf)
	} else {
		// try reading one more byte and see if it succeeds.
		decoder.set_limit(BOMB_LIMIT + 1);
		if decoder.read(&mut [0]).ok().map_or(false, |read| read == 0) {
			Ok(buf)
		} else {
			Err(Error::PossibleBomb)
		}
	}
}

#[cfg(not(target_os = "unknown"))]
fn decode_zstd(blob: &[u8]) -> Result<Vec<u8>, Error> {
	let decoder = zstd::Decoder::new(blob).map_err(|_| Error::Invalid)?;

	read_from_decoder(decoder, blob.len())
}

#[cfg(target_os = "unknown")]
fn decode_zstd(mut blob: &[u8]) -> Result<Vec<u8>, Error> {
	let blob_len = blob.len();
	let decoder = ruzstd::streaming_decoder::StreamingDecoder::new(&mut blob)
		.map_err(|_| Error::Invalid)?;

	read_from_decoder(decoder, blob_len)
}

/// Decode a blob, if it indicates that it is compressed.
pub fn decode(blob: &[u8]) -> Result<Cow<[u8]>, Error> {
	if blob.starts_with(&ZSTD_PREFIX) {
		decode_zstd(&blob[ZSTD_PREFIX.len()..]).map(Into::into)
	} else {
		Ok(blob.into())
	}
}

/// Encode a blob as compressed. If the blob's size is over the bomb limit,
/// this will not compress the blob, as the decoder will not be able to be
/// able to differentiate it from a compression bomb.
#[cfg(not(target_os = "unknown"))]
pub fn compress(blob: &[u8]) -> Option<Vec<u8>> {
	use std::io::Write;

	if (blob.len() as u64) > BOMB_LIMIT {
		return None;
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
	use std::io::Write;

	#[test]
	fn refuse_to_encode_over_limit() {
		let mut v = vec![0; (BOMB_LIMIT + 1) as usize];
		assert!(compress(&v).is_none());

		let _ = v.pop();
		assert!(compress(&v).is_some());

	}

	#[test]
	fn compress_and_decode() {
		let v = vec![0; 10_000];

		let compressed = compress(&v).unwrap();

		assert!(compressed.starts_with(&ZSTD_PREFIX));
		assert_eq!(&decode(&compressed).unwrap()[..], &v[..])
	}

	#[test]
	fn decodes_only_when_magic() {
		let v = vec![0; 10_000];

		assert_eq!(&decode(&v).unwrap()[..], &v[..]);
	}

	#[test]
	fn possible_bomb_fails() {
		let encoded_bigger_than_bomb = vec![0; (BOMB_LIMIT + 1) as usize];
		let mut buf = ZSTD_PREFIX.to_vec();

		{
			let mut v = zstd::Encoder::new(&mut buf, 3).unwrap().auto_finish();
			v.write_all(&encoded_bigger_than_bomb[..]).unwrap();
		}

		assert_eq!(decode(&buf[..]).err(), Some(Error::PossibleBomb));
	}
}
