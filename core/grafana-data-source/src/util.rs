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

/// Get the current unix timestamp in milliseconds.
pub fn now_millis() -> i64 {
	chrono::Utc::now().timestamp_millis()
}

// find the index of a timestamp
pub fn find_index(slice: &[(f32, i64)], timestamp: i64) -> usize {
	slice.binary_search_by_key(&timestamp, |&(_, timestamp)| timestamp)
		.unwrap_or_else(|index| index)
}

// Evenly select up to `num_points` points from a slice
pub fn select_points<T: Copy>(slice: &[T], num_points: usize) -> Vec<T> {
	if num_points == 0 {
		return Vec::new();
	} else if num_points >= slice.len() {
		return slice.to_owned();
	}

	(0 .. num_points - 1)
		.map(|i| slice[i * slice.len() / (num_points - 1)])
		.chain(slice.last().cloned())
		.collect()
}

#[test]
fn test_select_points() {
	let array = [1, 2, 3, 4, 5];
	assert_eq!(select_points(&array, 0), Vec::<u8>::new());
	assert_eq!(select_points(&array, 1), vec![5]);
	assert_eq!(select_points(&array, 2), vec![1, 5]);
	assert_eq!(select_points(&array, 3), vec![1, 3, 5]);
	assert_eq!(select_points(&array, 4), vec![1, 2, 4, 5]);
	assert_eq!(select_points(&array, 5), vec![1, 2, 3, 4, 5]);
	assert_eq!(select_points(&array, 6), vec![1, 2, 3, 4, 5]);
}
