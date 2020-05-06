// Copyright 2020 Parity Technologies (UK) Ltd.
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
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Common fuzzing utils.

/// converts x into the range [a, b] in a pseudo-fair way.
pub fn to_range(x: usize, a: usize, b: usize) -> usize {
	// does not work correctly if b < 2*a
	assert!(b > 2 * a);
	let collapsed = x % b;
	if collapsed >= a {
		collapsed
	} else {
		collapsed + a
	}
}
