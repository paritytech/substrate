// This file is part of Substrate.

// Copyright (C) 2020-2020 Parity Technologies (UK) Ltd.
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

//! History state storage and management.

/// Forkable state management implementations.
pub mod tree;

/// Linear state management implementations.
pub mod linear {

	use crate::{Latest, Management, ManagementRef, Migrate, LinearManagement};
	use sp_std::ops::{AddAssign, SubAssign};

	// This is for small state as there is no double
	// mapping an some operation goes through full scan.
	pub struct LinearInMemoryManagement<H, S, V> {
		mapping: sp_std::collections::btree_map::BTreeMap<H, S>,
		start_treshold: S,
		current_state: S,
		neutral_element: Option<V>,
		changed_treshold: bool,
		can_append: bool,
	}

	impl<H, S, V> LinearInMemoryManagement<H, S, V> {
		// TODO should use a builder but then we need
		// to change Management trait
		pub fn define_neutral_element(mut self, n: V) -> Self {
			self.neutral_element = Some(n);
			self
		}
	}

	impl<H, S: AddAssign<u32>, V> LinearInMemoryManagement<H, S, V> {
		pub fn prune(&mut self, nb: usize) {
			self.changed_treshold = true;
			self.start_treshold += nb as u32
		}
	}

	impl<H: Ord, S: Clone, V: Clone> ManagementRef<H> for LinearInMemoryManagement<H, S, V> {
		type S = S;
		type GC = (S, Option<V>);
		type Migrate = (S, Self::GC);
		fn get_db_state(&mut self, state: &H) -> Option<Self::S> {
			self.mapping.get(state).cloned()
		}
		fn get_gc(&self) -> Option<crate::Ref<Self::GC>> {
			if self.changed_treshold {
				Some(crate::Ref::Owned((self.start_treshold.clone(), self.neutral_element.clone())))
			} else {
				None
			}
		}
	}

	impl<
	H: Ord + Clone,
	S: Default + Clone + AddAssign<u32> + Ord,
	V: Clone,
	> Management<H> for LinearInMemoryManagement<H, S, V> {
		type SE = Latest<S>;
		fn init() -> (Self, Self::S) {
			let state = S::default();
			let current_state = S::default();
			let mapping = Default::default();
			(LinearInMemoryManagement {
				mapping,
				start_treshold: state.clone(),
				current_state,
				neutral_element: None,
				changed_treshold: false,
				can_append: true,
			}, state)
		}

		fn init_state(&mut self) -> Self::SE {
			Latest::unchecked_latest(self.start_treshold.clone())
		}

		fn get_db_state_mut(&mut self, state: &H) -> Option<Self::SE> {
			if let Some(state) = self.mapping.get(state) {
				let latest = self.mapping.values().max()
					.map(Clone::clone)
					.unwrap_or(S::default());
				if state == &latest {
					return Some(Latest::unchecked_latest(latest))
				}
			}
			None
		}

		fn latest_state(&mut self) -> Self::SE {
			Latest::unchecked_latest(self.current_state.clone())
		}

		fn latest_external_state(&mut self) -> Option<H> {
			// Actually unimplemented
			None
		}

		fn force_latest_external_state(&mut self, _state: H) { }

		fn reverse_lookup(&mut self, state: &Self::S) -> Option<H> {
			// TODO could be the closest valid and return non optional!!!! TODO
			self.mapping.iter()
				.find(|(_k, v)| v == &state)
				.map(|(k, _v)| k.clone())
		}

		fn get_migrate(self) -> (Migrate<H, Self>, Self::Migrate) {
			unimplemented!()
		}

		fn applied_migrate(&mut self) {
			self.changed_treshold = false;
			//self.start_treshold = gc.0; // TODO from backed inner state

			unimplemented!()
		}
	}

	impl<
	H: Ord + Clone,
	S: Default + Clone + SubAssign<S> + AddAssign<u32> + Ord,
	V: Clone,
	> LinearManagement<H> for LinearInMemoryManagement<H, S, V> {
		fn append_external_state(&mut self, state: H) -> Option<Self::S> {
			if !self.can_append {
				return None;
			}
			self.current_state += 1;
			self.mapping.insert(state, self.current_state.clone());
			Some(self.current_state.clone())
		}

		fn drop_last_state(&mut self) -> Self::S {
			let mut v = S::default();
			if self.current_state != v {
				v += 1;
				self.current_state -= v;
			}
			self.can_append = true;
			self.current_state.clone()
		}
	}
}
