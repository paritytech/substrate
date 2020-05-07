// This file is part of Substrate.

// Copyright (C) 2017-2020 Parity Technologies (UK) Ltd.
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

//! Substrate customizable serde serializer.
//!
//! The idea is that we can later change the implementation
//! to something more compact, but for now we're using JSON.

#![warn(missing_docs)]

pub use serde_json::{from_str, from_slice, from_reader, Result, Error};

const PROOF: &str = "Serializers are infallible; qed";

/// Serialize the given data structure as a pretty-printed String of JSON.
pub fn to_string_pretty<T: serde::Serialize + ?Sized>(value: &T) -> String {
	serde_json::to_string_pretty(value).expect(PROOF)
}

/// Serialize the given data structure as a JSON byte vector.
pub fn encode<T: serde::Serialize + ?Sized>(value: &T) -> Vec<u8> {
	serde_json::to_vec(value).expect(PROOF)
}

/// Serialize the given data structure as JSON into the IO stream.
pub fn to_writer<W: ::std::io::Write, T: serde::Serialize + ?Sized>(writer: W, value: &T) -> Result<()> {
	serde_json::to_writer(writer, value)
}
