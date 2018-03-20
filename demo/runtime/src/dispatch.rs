// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate Demo.

// Substrate Demo is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate Demo is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate Demo.  If not, see <http://www.gnu.org/licenses/>.

//! Dispatch system. Just dispatches calls.

use {runtime, runtime_support, consensus};

impl_meta_dispatch! {
	pub mod public;
	path public;
	trait runtime_support::PublicPass;
	Session(mod runtime::session) = 1;
	Staking(mod runtime::staking) = 2;
	Timestamp(mod runtime::timestamp) = 3;
	Democracy(mod runtime::democracy) = 5;
	Council(mod runtime::council) = 6;
	CouncilVote(mod runtime::council_vote) = 7;
}

impl_meta_dispatch! {
	pub mod privileged;
	path privileged;
	trait runtime_support::PrivPass;
	Consensus(mod consensus) = 0;
	Session(mod runtime::session) = 1;
	Staking(mod runtime::staking) = 2;
	Democracy(mod runtime::democracy) = 5;
	Council(mod runtime::council) = 6;
	CouncilVote(mod runtime::council_vote) = 7;
}

pub use self::privileged::Call as PrivCall;
pub use self::public::Call as PubCall;
