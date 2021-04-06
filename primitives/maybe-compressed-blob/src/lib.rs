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

// An arbitrary prefix, that indicates a blob beginning with should be decoded with
// Zstd compression.
const ZSTD_PREFIX: [u8; 8] = [82, 188, 83, 118, 70, 219, 142, 5];

/// The maximum size for compressed blobs.
pub const BOMB_LIMIT: usize = 50 * 1024 * 1024;

/// A possible bomb was encountered.
#[derive(Debug, Clone, Copy)]
pub struct PossibleBomb;

impl std::fmt::Display for PossibleBomb {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "Possible compression bomb encountered");
	}
}

impl std::error::Error for PossibleBomb { }

/// Decode a blob, if it indicates that it is compressed.
pub fn decode(blob: &[u8]) -> Result<Cow<[u8]>, PossibleBomb> {
	if blob.starts_with(ZSTD_PREFIX) {
		unimplemented!()
	} else {
		Ok(blob.into())
	}
}

/// Encode a blob as compressed. If the blob's size is over the bomb limit,
/// this will not compress the blob, as the decoder will not be able to be
/// able to differentiate it from a compression bomb.
#[cfg(feature = "encode")]
pub fn encode(blob: Vec<u8>) -> Vec<u8> {
	if blob.len() > BOMB_LIMIT {
		return blob;
	}
}
