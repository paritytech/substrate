// This file is part of Substrate.

// Copyright (C) 2020 Parity Technologies (UK) Ltd.
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

/// The error type for database operations.
#[derive(Debug)]
pub struct DatabaseError(pub Box<dyn std::error::Error + Send>);

impl std::fmt::Display for DatabaseError {
	fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
		write!(f, "{}", self.0)
	}
}

impl std::error::Error for DatabaseError {
	fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
		None
	}
}

/// A specialized `Result` type for database operations.
pub type Result<T> = std::result::Result<T, DatabaseError>;
