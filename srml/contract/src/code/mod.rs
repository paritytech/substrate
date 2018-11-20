// Copyright 2018 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate. If not, see <http://www.gnu.org/licenses/>.

use codec::Compact;
use ::Trait;

mod prepare;

#[derive(Encode, Decode)]
pub struct CodeHash<Hash>(Hash);

#[derive(Encode, Decode)]
pub struct MemoryDefinition {
	#[codec(compact)]
	initial: u32,
	#[codec(compact)]
	maximum: u32,
}

#[derive(Encode, Decode)]
pub struct InstrumentedWasmModule {
	memory_def: MemoryDefinition,
	/// Code instrumented with the latest schedule.
	code: Vec<u8>,
}

pub fn save<T: Trait>(original_code: Vec<u8>) {
	panic!()

}

pub fn load<T: Trait>(hash: CodeHash<T::Hash>) -> InstrumentedWasmModule {
	// TODO: Load the version of schedule for the code. Reinstrument if it doesn't match.
	panic!()
}

