// This file is part of Substrate.

// Copyright (C) 2015-2022 Parity Technologies (UK) Ltd.
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

use sp_std::{boxed::Box, vec::Vec};

/// Error type used for trie related errors.
#[derive(Debug, PartialEq, Eq, Clone)]
#[cfg_attr(feature = "std", derive(thiserror::Error))]
pub enum Error<H> {
	#[cfg_attr(feature = "std", error("Bad format"))]
	BadFormat,
	#[cfg_attr(feature = "std", error("Decoding failed: {0}"))]
	Decode(#[cfg_attr(feature = "std", source)] codec::Error),
	#[cfg_attr(
		feature = "std",
		error("Recorded key ({0:x?}) access with value as found={1}, but could not confirm with trie.")
	)]
	InvalidRecording(Vec<u8>, bool),
	#[cfg_attr(feature = "std", error("Trie error: {0:?}"))]
	TrieError(Box<trie_db::TrieError<H, Self>>),
}

impl<H> From<codec::Error> for Error<H> {
	fn from(x: codec::Error) -> Self {
		Error::Decode(x)
	}
}

impl<H> From<Box<trie_db::TrieError<H, Self>>> for Error<H> {
	fn from(x: Box<trie_db::TrieError<H, Self>>) -> Self {
		Error::TrieError(x)
	}
}
