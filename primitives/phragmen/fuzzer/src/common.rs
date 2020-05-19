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
