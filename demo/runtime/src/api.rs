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

use runtime;
use Executive;

impl_stubs!(
	authorities => |()| runtime::Consensus::authorities(),
	initialise_block => |header| Executive::initialise_block(&header),
	apply_extrinsic => |extrinsic| Executive::apply_extrinsic(extrinsic),
	execute_block => |block| Executive::execute_block(block),
	finalise_block => |()| Executive::finalise_block()
	/*validator_count => |()| session::validator_count(),
	validators => |()| session::validators(),*/
);
