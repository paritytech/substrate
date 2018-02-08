// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Polkadot.

// Polkadot is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Polkadot is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Polkadot.  If not, see <http://www.gnu.org/licenses/>.

use runtime::{system, parachains, consensus, session};

impl_stubs!(
	execute_block => |block| system::internal::execute_block(block),
	execute_transaction => |(header, utx)| system::internal::execute_transaction(utx, header),
	finalise_block => |header| system::internal::finalise_block(header),
	validator_count => |()| session::validator_count(),
	validators => |()| session::validators(),
	authorities => |()| consensus::authorities(),
	duty_roster => |()| parachains::calculate_duty_roster()
);
