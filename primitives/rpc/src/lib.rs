// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Substrate RPC primitives and utilities.

#![warn(missing_docs)]

pub mod list;
pub mod number;
pub mod tracing;

/// A util function to assert the result of serialization and deserialization is the same.
#[cfg(test)]
pub(crate) fn assert_deser<T>(s: &str, expected: T)
where
	T: std::fmt::Debug + serde::ser::Serialize + serde::de::DeserializeOwned + PartialEq,
{
	assert_eq!(serde_json::from_str::<T>(s).unwrap(), expected);
	assert_eq!(serde_json::to_string(&expected).unwrap(), s);
}
