// Copyright 2019 Parity Technologies (UK) Ltd.
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

/// Sort Sassafras proof with the given limit, and into inside-out order.
/// The smallest items are on both side of the array, with the largest in
/// the middle.
pub fn sortition<T: Ord + Clone>(input: &[T], limit: usize) -> Vec<T> {
	let mut ret = input.to_vec();
	ret.sort();

	while ret.len() > limit {
		ret.pop();
	}

	if !ret.is_empty() {
		let half = ret.len() / 2;
		ret[half..].sort_by(|a, b| a.cmp(b).reverse());
	}

	ret
}
