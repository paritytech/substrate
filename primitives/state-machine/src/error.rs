// This file is part of Substrate.

// Copyright (C) 2019-2020 Parity Technologies (UK) Ltd.
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

/// State Machine Errors

use std::fmt;

/// State Machine Error bound.
///
/// This should reflect Wasm error type bound for future compatibility.
pub trait Error: 'static + fmt::Debug + fmt::Display + Send {}

impl<T: 'static + fmt::Debug + fmt::Display + Send> Error for T {}

/// Externalities Error.
///
/// Externalities are not really allowed to have errors, since it's assumed that dependent code
/// would not be executed unless externalities were available. This is included for completeness,
/// and as a transition away from the pre-existing framework.
#[derive(Debug, Eq, PartialEq)]
pub enum ExecutionError {
	/// Backend error.
	Backend(String),
	/// The entry `:code` doesn't exist in storage so there's no way we can execute anything.
	CodeEntryDoesNotExist,
	/// Backend is incompatible with execution proof generation process.
	UnableToGenerateProof,
	/// Invalid execution proof.
	InvalidProof,
}

impl fmt::Display for ExecutionError {
	fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "Externalities Error") }
}
