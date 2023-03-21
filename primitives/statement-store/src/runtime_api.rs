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

use codec::{Decode, Encode};
use scale_info::TypeInfo;
use sp_runtime::RuntimeDebug;
use crate::Statement;

/// Information concerning a valid statement.
#[derive(Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub struct ValidStatement {
	pub priority: u64,
}

/// An invalid statement.
#[derive(Clone, PartialEq, Eq, Encode, Decode, Copy, RuntimeDebug, TypeInfo)]
pub enum InvalidStatement {
	BadProof,
	NoProof,
	InternalError,
}

/// The source of the statement.
///
/// Depending on the source we might apply different validation schemes.
#[derive(Copy, Clone, PartialEq, Eq, Encode, Decode, RuntimeDebug, TypeInfo)]
pub enum StatementSource {
	/// Statement is coming from the on-chain worker.
	Chain,
	/// Statement has been received from the gossip network.
	Network,
	/// Statement has been submitted over the RPC api.
	Rpc,
}

impl StatementSource {
	pub fn can_be_resubmitted(&self) -> bool {
		match self {
			StatementSource::Chain | StatementSource::Rpc => true,
			StatementSource::Network => false,
		}
	}
}

sp_api::decl_runtime_apis! {
	/// Runtime API trait for statement validation.
	pub trait ValidateStatement {
		/// Validate the statement.
		fn validate_statement(
			source: StatementSource,
			statement: Statement,
		) -> Result<ValidStatement, InvalidStatement>;
	}
}

