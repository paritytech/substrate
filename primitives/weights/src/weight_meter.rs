// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

//! Contains the `WeightCounter` primitive.

struct WeightCounter {
	used: Weight,
	limit: Weight,
}
impl WeightCounter {
	fn check_accrue(&mut self, w: Weight) -> bool {
		let test = self.used.saturating_add(w);
		if test.any_gt(self.limit) {
			false
		} else {
			self.used = test;
			true
		}
	}
	fn can_accrue(&mut self, w: Weight) -> bool {
		self.used.saturating_add(w).all_lte(self.limit)
	}
}
