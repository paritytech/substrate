// This file is part of Substrate.

// Copyright (C) 2021 Subspace Labs, Inc.
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

//! Spartan-based PoR.

use ring::{digest, hmac};
use std::convert::TryInto;
use std::io::Write;

const PRIME_SIZE_BYTES: usize = 8;
const PIECE_SIZE: usize = 4096;
const GENESIS_PIECE_SEED: &str = "spartan";
const ENCODE_ROUNDS: usize = 1;
pub const SIGNING_CONTEXT: &[u8] = b"FARMER";

pub type Piece = [u8; PIECE_SIZE];
pub type Tag = [u8; PRIME_SIZE_BYTES];
pub type Salt = [u8; 32];

pub struct Spartan {
    instance: spartan_codec::Spartan<PRIME_SIZE_BYTES, PIECE_SIZE>,
}

impl Spartan {
    pub fn new() -> Self {
        Self {
            instance: spartan_codec::Spartan::<PRIME_SIZE_BYTES, PIECE_SIZE>::new(
                genesis_piece_from_seed(GENESIS_PIECE_SEED),
            ),
        }
    }

    pub fn is_encoding_valid(&self, encoding: Piece, public_key: &[u8], nonce: u64) -> bool {
        self.instance
            .is_valid(encoding, hash_public_key(public_key), nonce, ENCODE_ROUNDS)
    }
}

pub fn is_commitment_valid(encoding: &Piece, tag: &Tag, salt: &Salt) -> bool {
    let correct_tag = create_tag(encoding, salt);
    &correct_tag == tag
}

fn genesis_piece_from_seed(seed: &str) -> Piece {
    let mut piece = [0u8; PIECE_SIZE];
    let mut input = seed.as_bytes().to_vec();
    for mut chunk in piece.chunks_mut(digest::SHA256.output_len) {
        input = digest::digest(&digest::SHA256, &input).as_ref().to_vec();
        chunk.write_all(input.as_ref()).unwrap();
    }
    piece
}

fn hash_public_key(public_key: &[u8]) -> [u8; PRIME_SIZE_BYTES] {
    let mut array = [0u8; PRIME_SIZE_BYTES];
    let hash = digest::digest(&digest::SHA256, public_key);
    array.copy_from_slice(&hash.as_ref()[..PRIME_SIZE_BYTES]);
    array
}

fn create_tag(encoding: &[u8], salt: &[u8]) -> Tag {
    let key = hmac::Key::new(hmac::HMAC_SHA256, salt);
    hmac::sign(&key, encoding).as_ref()[0..8]
        .try_into()
        .unwrap()
}
