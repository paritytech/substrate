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

//! Tree historied data historied db implementations.

// TODO remove "previous code" expect.

use super::{HistoriedValue, Data, DataMut, DataRef, DataRefMut,
	DataSlices, DataSliceRanges, UpdateResult, Value, ValueRef,
	DataBasis};
use crate::backend::{LinearStorage, LinearStorageRange, LinearStorageSlice, LinearStorageMem};
use crate::historied::linear::{Linear, LinearState, LinearGC};
use crate::management::tree::{ForkPlan, DeltaTreeStateGc, MultipleGc, MultipleMigrate};
use sp_std::marker::PhantomData;
use crate::Latest;
use crate::{Context, ContextBuilder, InitFrom, DecodeWithContext, Trigger};
use codec::{Encode, Input};
use derivative::Derivative;
use core::default::Default;


// Adapter such as in linear are getting too complex for tree, just using
// macros to remove duplicated code.
// Common code to get from tree.
// Lookup first linear storage in parallel (until incorrect state ordering).
// Call second linear historied value afterward.
macro_rules! tree_get {
	($fn_name: ident, $return_type: ty, $branch_query: ident, $value_query: expr, $post_process: expr, $b: lifetime) => {
	fn $fn_name<$b>(&'a self, at: &<Self as DataBasis>::S) -> Option<$return_type> {
		// note that we expect branch index to be linearily set
		// along a branch (no state containing unordered branch_index
		// and no history containing unorderd branch_index).
		let mut next_branch_index = self.branches.last();
		for (state_branch_range, state_branch_index) in at.iter() {
			while let Some(branch_ix) = next_branch_index {
				let branch_index = &self.branches.get_state(branch_ix);
				if branch_index < &state_branch_index {
					break;
				} else if branch_index == &state_branch_index {
					// TODO add a lower bound check (maybe debug_assert it only).
					let mut upper_bound = state_branch_range.end.clone();
					upper_bound -= BI::one();
					let branch = self.branches.$branch_query(branch_ix).value;
					if let Some(result) = $value_query(&branch, &upper_bound) {
						return Some($post_process(result, branch, branch_ix))
					}
				}
				next_branch_index = self.branches.previous_index(branch_ix);
			}
		}

		// composite part.
		while let Some(branch_ix) = next_branch_index {
			let branch_index = &self.branches.get_state(branch_ix);
			if branch_index <= &at.composite_treshold.0 {
				let branch = self.branches.$branch_query(branch_ix).value;
				if let Some(result) = $value_query(&branch, &at.composite_treshold.1) {
					return Some($post_process(result, branch, branch_ix))
				}
			}
			next_branch_index = self.branches.previous_index(branch_ix);
		}
	
		None
	}
	}
}

#[derive(Derivative, Debug, Clone, Encode)]
#[derivative(PartialEq(bound="D: PartialEq"))]
pub struct Tree<I, BI, V, D: Context, BD: Context> {
	branches: D,
	#[codec(skip)]
	#[derivative(PartialEq="ignore" )]
	init: D::Context,
	#[codec(skip)]
	#[derivative(PartialEq="ignore" )]
	init_child: BD::Context,
	#[codec(skip)]
	_ph: PhantomData<(I, BI, V, BD)>,
}

impl<I, BI, V, D, BD> DecodeWithContext for Tree<I, BI, V, D, BD>
	where
		D: DecodeWithContext,
		BD: DecodeWithContext,
{
	fn decode_with_context<IN: Input>(input: &mut IN, init: &Self::Context) -> Option<Self> {
		D::decode_with_context(input, &init.0).map(|branches|
			Tree {
				branches,
				init: init.0.clone(),
				init_child: init.1.clone(),
				_ph: PhantomData,
			}
		)
	}
}

impl<I, BI, V, D: Context, BD: Context> Context for Tree<I, BI, V, D, BD> {
	type Context = (D::Context, BD::Context);
}

impl<I, BI, V, D: Context + Trigger, BD: Context> Trigger for Tree<I, BI, V, D, BD> {
	const TRIGGER: bool = <D as Trigger>::TRIGGER;

	fn trigger_flush(&mut self) {
		if Self::TRIGGER {
			self.branches.trigger_flush();
		}
	}
}

impl<I, BI, V, D: InitFrom, BD: InitFrom> InitFrom for Tree<I, BI, V, D, BD> {
	fn init_from(init: Self::Context) -> Self {
		Tree {
			branches: D::init_from(init.0.clone()),
			init: init.0,
			init_child: init.1,
			_ph: PhantomData,
		}
	}
}

type Branch<I, BI, V, BD> = HistoriedValue<Linear<V, BI, BD>, I>;

impl<I, BI, V, BD> Branch<I, BI, V, BD>
	where
		I: Clone + Encode,
		BI: LinearState,
		V: Value + Clone + Eq,
		BD: LinearStorage<V::Storage, BI>,
{
	pub fn new(value: V, state: &(I, BI), init: &BD::Context) -> Self {
		let (branch_index, index) = state.clone();
		let index = Latest::unchecked_latest(index); // TODO cast ptr?
		let init = if BD::Context::USE_INDEXES {
			let index = state.0.encode(); // TODO force compact encode?
			// parent index set at build.
			init.with_indexes(&[], index.as_slice())
		} else {
			init.clone()
		};
		let history = Linear::new(value, &index, init);
		Branch {
			state: branch_index,
			value: history,
		}
	}
}

impl<I, BI, V, D, BD> DataBasis for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: Value + Clone,
		D: LinearStorage<Linear<V, BI, BD>, I>, // TODO rewrite to be linear storage of BD only.
		BD: LinearStorage<V::Storage, BI>,
{
	type S = ForkPlan<I, BI>;
	type Index = (I, BI);

	fn contains(&self, at: &Self::S) -> bool {
		self.get(at).is_some() // TODO avoid clone??
	}

	fn is_empty(&self) -> bool {
		// This implies empty branch get clean correctly.
		self.branches.len() == 0
	}
}

impl<I, BI, V, D, BD> Data<V> for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: Value + Clone,
		D: LinearStorage<Linear<V, BI, BD>, I>, // TODO rewrite to be linear storage of BD only.
		BD: LinearStorage<V::Storage, BI>,
{
	tree_get!(get, V, get, |b: &Linear<V, BI, BD>, ix| b.get(ix), |r, _, _| r, 'a);
}

impl<I, BI, V, D, BD> DataRef<V> for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: ValueRef + Clone,
		D: LinearStorageMem<Linear<V, BI, BD>, I>,
		BD: LinearStorageMem<V::Storage, BI>,
{
	tree_get!(get_ref, &V, get_ref, |b: &'a Linear<V, BI, BD>, ix| b.get_ref(ix), |r, _, _| r, 'a);
}

impl<I, BI, V, D, BD> DataMut<V> for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone + Encode,
		BI: LinearState,
		V: Value + Clone + Eq,
		D: LinearStorage<Linear<V, BI, BD>, I>,
		BD: LinearStorage<V::Storage, BI> + Trigger,
{
	type SE = Latest<(I, BI)>;
	type GC = MultipleGc<I, BI>;
	type Migrate = MultipleMigrate<I, BI>;

	fn new(value: V, at: &Self::SE, init: Self::Context) -> Self {
		let mut v = D::init_from(init.0.clone());
		v.push(Branch::new(value, at.latest(), &init.1));
		Tree {
			branches: v,
			init: init.0,
			init_child: init.1,
			_ph: PhantomData,
		}
	}

	fn set(&mut self, value: V, at: &Self::SE) -> UpdateResult<()> {
		// Warn dup code, can be merge if change set to return previ value: with
		// ref refact will be costless
		let (branch_index, index) = at.latest();
		let mut insert_at = None;
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				let mut branch = self.branches.get(branch_ix);
				return match branch.value.set(value, &index) {
					UpdateResult::Changed(_) => {
						self.branches.emplace(branch_ix, branch);
						UpdateResult::Changed(())
					},
					UpdateResult::Cleared(_) => {
						self.remove_branch(branch_ix);
						if self.branches.len() == 0 {
							UpdateResult::Cleared(())
						} else {
							UpdateResult::Changed(())
						}
					},
					UpdateResult::Unchanged => UpdateResult::Unchanged,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
		}
		let branch = Branch::new(value, at.latest(), &self.init_child);
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		UpdateResult::Changed(())
	}

	fn discard(&mut self, at: &Self::SE) -> UpdateResult<Option<V>> {
		let (branch_index, index) = at.latest();
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				let mut branch = self.branches.get(branch_ix);
				return match branch.value.discard(&index) {
					UpdateResult::Changed(v) => {
						self.branches.emplace(branch_ix, branch);
						UpdateResult::Changed(v)
					},
					UpdateResult::Cleared(v) => {
						self.remove_branch(branch_ix);
						if self.branches.len() == 0 {
							UpdateResult::Cleared(v)
						} else {
							UpdateResult::Changed(v)
						}
					},
					UpdateResult::Unchanged => UpdateResult::Unchanged,
				};
			}
			if &iter_branch_index < branch_index {
				break;
			}
		}

		UpdateResult::Unchanged
	}

	fn gc(&mut self, gc: &Self::GC) -> UpdateResult<()> {
		match gc {
			MultipleGc::Journaled(gc) => self.journaled_gc(gc),
		}
	}

	fn is_in_migrate((index, linear_index) : &Self::Index, gc: &Self::Migrate) -> bool {
		match gc {
			MultipleMigrate::Noops => (),
			MultipleMigrate::JournalGc(gc) => {
				if let Some(new_start) = gc.pruning_treshold.as_ref() {
					if linear_index <= &new_start {
						return true;
					}
				}
				if let Some(br) = gc.storage.get(&index) {
					return if let Some(bi) = br.0.as_ref() {
						bi <= linear_index
					} else {
						true
					};
				}
			},
		}
		false
	}

	fn migrate(&mut self, mig: &Self::Migrate) -> UpdateResult<()> {
		let mut result = UpdateResult::Unchanged;

		match mig {
			MultipleMigrate::JournalGc(gc) => {
				result = self.journaled_gc(gc);
				if let UpdateResult::Cleared(()) = result {
					return UpdateResult::Cleared(());
				}
				let mut new_branch: Option<Branch<I, BI, V, BD>> = None;
				let mut i = 0;
				// merge all less than composite treshold in composite treshold index branch.
				loop {
					if let Some(index) = self.branches.lookup(i) {
						let mut branch = self.branches.get(index);
						if branch.state <= gc.composite_treshold.0 {
							if let Some(new_branch) = new_branch.as_mut() {
								for i in 0.. {
									if let Some(h) = branch.value.storage().lookup(i) {
										let h = branch.value.storage().get(h);
										new_branch.value.storage_mut().push(h);
									} else {
										break;
									}
								}
							} else {
								branch.state = gc.composite_treshold.0.clone();
								new_branch = Some(branch);
							}
						} else {
							break;
						}
					} else {
						break;
					}
					i += 1;
				}
				if let Some(new_branch) = new_branch {
					if i == self.branches.len() {
						self.branches.clear();
						self.branches.push(new_branch);
					} else {
						self.truncate_branches_until(i);
						self.branches.insert_lookup(0, new_branch);
					}
				}
			},
			MultipleMigrate::Noops => (),
		}

		if let UpdateResult::Changed(()) = result {
			if self.branches.len() == 0 {
				result = UpdateResult::Cleared(());
			}
		}
		result
	}
}


impl<I, BI, V, D, BD> Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: Value + Clone + Eq,
		D: LinearStorage<Linear<V, BI, BD>, I>,
		BD: LinearStorage<V::Storage, BI> + Trigger,
{
	fn journaled_gc(&mut self, gc: &DeltaTreeStateGc<I, BI>) -> UpdateResult<()> {
		// for all branch check if in deleted.
		// Also apply new start on all.
		let mut result = UpdateResult::Unchanged;
		let start_history = gc.pruning_treshold.as_ref();
		let mut first_new_start = false;
		let mut next_branch_index = self.branches.last();
		while let Some(branch_ix) = next_branch_index {
			let mut branch = self.branches.get(branch_ix);
			let new_start = if branch.state <= gc.composite_treshold.0 {
				match start_history.as_ref() {
					None => None,
					Some(n_start) => {
						if first_new_start {
							self.remove_branch(branch_ix);
							result = UpdateResult::Changed(());
							next_branch_index = self.branches.previous_index(branch_ix);
							continue;
						} else {
							if let Some(b) = branch.value.storage().lookup(0) {
								let b = branch.value.storage().get(b);
								if &b.state < n_start {
									first_new_start = true;
								}
							}
							start_history.cloned()
						}
					},
				}
			} else {
				None
			};

			if let Some(mut gc) = if let Some(change) = gc.storage.get(&branch.state) {
				if change.0.is_none() {
					self.remove_branch(branch_ix);
					result = UpdateResult::Changed(());
					None
				} else {
					Some(LinearGC {
						new_start,
						new_end: change.0.clone(),
					})
				}
			} else {
				if first_new_start {
					Some(LinearGC {
						new_start,
						new_end: None,
					})
				} else {
					None
				}
			} {
				match branch.value.gc(&mut gc) {
					UpdateResult::Unchanged => (),
						UpdateResult::Changed(_) => { 
						self.branches.emplace(branch_ix, branch);
						result = UpdateResult::Changed(());
					},
					UpdateResult::Cleared(_) => {
						self.remove_branch(branch_ix);
						result = UpdateResult::Changed(());
					}
				}
			}
			next_branch_index = self.branches.previous_index(branch_ix);
		}

		if let UpdateResult::Changed(()) = result {
			if self.branches.len() == 0 {
				result = UpdateResult::Cleared(());
			}
		}

		result
	}

	fn trigger_clear_branch(&mut self, branch_ix: D::Index) {
		let mut branch = self.branches.get(branch_ix); // TODO have a
		// variant of remove that return old value.
		// Also TODO a get_ref_mut version
		branch.value.storage_mut().clear();
		branch.trigger_flush();
	}

	// any removal of branch need to trigger its old value.
	fn remove_branch(&mut self, branch_ix: D::Index) {
		if BD::TRIGGER {
			self.trigger_clear_branch(branch_ix);
		}
		self.branches.remove(branch_ix);
	}

	// trigger when we truncate or truncate_until.
	// Warning all indexes are inclusive
	fn truncate_branches_until(&mut self, end: usize) {
		if BD::TRIGGER {
			let nb = end;
			if nb > 0 {
				let mut index = self.branches.lookup(end - 1);
				for _ in 0..nb {
					if let Some(branch_index) = index {
						self.trigger_clear_branch(branch_index);
						index = self.branches.previous_index(branch_index);
					} else {
						break;
					}
				}
			}
		}
		self.branches.truncate_until(end);
	}
}

#[cfg(test)]
pub(crate) trait TreeTestMethods {
	fn nb_internal_history(&self) -> usize;
	fn nb_internal_branch(&self) -> usize;
}

#[cfg(test)]
impl<I, BI, V, D, BD> TreeTestMethods for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: Value + Clone + Eq,
		D: LinearStorage<Linear<V, BI, BD>, I>,
		BD: LinearStorage<V::Storage, BI>,
{
	fn nb_internal_history(&self) -> usize {
		let mut nb = 0;
		for index in self.branches.rev_index_iter() {
			let branch = self.branches.get(index);
			nb += branch.value.storage().len();
		}
		nb
	}

	fn nb_internal_branch(&self) -> usize {
		self.branches.len()
	}
}

impl<I, BI, V, D, BD> DataRefMut<V> for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone + Encode,
		BI: LinearState,
		V: ValueRef + Clone + Eq,
		D: LinearStorageMem<Linear<V, BI, BD>, I>,
		BD: LinearStorageMem<V::Storage, BI, Context = D::Context> + Trigger,
{
	fn get_mut(&mut self, at: &Self::SE) -> Option<&mut V> {
		let (branch_index, index) = at.latest();
		for branch_ix in self.branches.rev_index_iter() {
			let iter_branch_index = self.branches.get_state(branch_ix);
			if &iter_branch_index == branch_index {
				let branch = self.branches.get_ref_mut(branch_ix);
				let index = Latest::unchecked_latest(index.clone());
				return branch.value.get_mut(&index);
			}
			if &iter_branch_index < branch_index {
				break;
			}
		}
		None
	}

	fn set_mut(&mut self, value: V, at: &Self::SE) -> UpdateResult<Option<V>> {
		// Warn dup code, can be merge if change set to return previ value: with
		// ref refact will be costless
		let (branch_index, index) = at.latest();
		let mut insert_at = None;
		let mut next_branch_index = self.branches.last();
		while let Some(branch_ix) = next_branch_index {
			let branch = self.branches.get_ref_mut(branch_ix);
			let iter_branch_index = &branch.state;
			if iter_branch_index == branch_index {
				let index = Latest::unchecked_latest(index.clone());
				return branch.value.set_mut(value, &index);
			}
			if iter_branch_index < branch_index {
				break;
			}
			insert_at = Some(branch_ix);
			next_branch_index = self.branches.previous_index(branch_ix);
		}
		let branch = Branch::new(value, at.latest(), &self.init_child);
		if let Some(index) = insert_at {
			self.branches.insert(index, branch);
		} else {
			self.branches.push(branch);
		}
		UpdateResult::Changed(None)
	}
}

#[cfg(feature = "temp-size-impl")]
type LinearBackendTempSize = crate::backend::in_memory::MemoryOnly<Option<Vec<u8>>, u64>;
#[cfg(feature = "temp-size-impl")]
type TreeBackendTempSize = crate::backend::in_memory::MemoryOnly<Linear<Option<Vec<u8>>, u64, LinearBackendTempSize>, u32>;

#[cfg(feature = "temp-size-impl")]
impl Tree<u32, u64, Option<Vec<u8>>, TreeBackendTempSize, LinearBackendTempSize> {
	/// Temporary function to get occupied stage.
	/// TODO replace by heapsizeof
	pub fn temp_size(&self) -> usize {
		let mut size = 0;
		for i in self.branches.rev_index_iter() {
			let b = self.branches.get_ref(i);
			size += 4; // branch index (using u32 as usize)
			size += b.value.temp_size();
		}
		size
	}
}

impl<'a, I, BI, V, D, BD> DataSlices<'a, V> for Tree<I, BI, V, D, BD>
	where
		I: Default + Ord + Clone,
		BI: LinearState,
		V: Value + Clone + AsRef<[u8]>,
		D: LinearStorageSlice<Linear<V, BI, BD>, I>,
		BD: AsRef<[u8]> + LinearStorageRange<'a, V::Storage, BI>,
{
	tree_get!(
		get_slice,
		&[u8],
		get_slice,
		|b: &'a [u8], ix| <Linear<V, BI, BD>>::get_range(b, ix),
		|result, b: &'a [u8], _| &b[result],
		'b
	);
}

#[cfg(feature = "force-data")]
pub mod force {
	use super::*;
	use crate::historied::force::ForceDataMut;

	impl<I, BI, V, D, BD> ForceDataMut<V> for Tree<I, BI, V, D, BD>
		where
			I: Default + Ord + Clone + Encode,
			BI: LinearState,
			V: Value + Clone + Eq,
			D: LinearStorage<Linear<V, BI, BD>, I>,
			BD: LinearStorage<V::Storage, BI> + Trigger,
	{
		fn force_set(&mut self, value: V, at: &Self::Index) -> UpdateResult<()> {
			// Warn dup code, just different linear function call from fn set,
			// and using directly index, TODO factor result handle at least.
			let (branch_index, index) = at;
			let mut insert_at = None;
			for branch_ix in self.branches.rev_index_iter() {
				let iter_branch_index = self.branches.get_state(branch_ix);
				if &iter_branch_index == branch_index {
					let index = index.clone();
					let mut branch = self.branches.get(branch_ix);
					return match branch.value.force_set(value, &index) {
						UpdateResult::Changed(_) => {
							self.branches.emplace(branch_ix, branch);
							UpdateResult::Changed(())
						},
						UpdateResult::Cleared(_) => {
							self.remove_branch(branch_ix);
							if self.branches.len() == 0 {
								UpdateResult::Cleared(())
							} else {
								UpdateResult::Changed(())
							}
						},
						UpdateResult::Unchanged => UpdateResult::Unchanged,
					};
				}
				if &iter_branch_index < branch_index {
					break;
				}
				insert_at = Some(branch_ix);
			}
			let branch = Branch::new(value, at, &self.init_child);
			if let Some(index) = insert_at {
				self.branches.insert(index, branch);
			} else {
				self.branches.push(branch);
			}
			UpdateResult::Changed(())
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;
	use crate::management::tree::test::test_states;
	use crate::{InitFrom, StateIndex};

	fn test_set_get_ref<T, V>(context: T::Context)
		where
			V: crate::historied::Value + std::fmt::Debug + From<u16> + Eq,
			T: InitFrom,
			T: crate::historied::DataBasis<S = ForkPlan<u32, u32>>,
			T: crate::historied::DataRef<V>,
			T: crate::historied::Data<V>,
			T: crate::historied::DataMut<
				V,
				Index = (u32, u32),
				SE = Latest<(u32, u32)>,
			>,
	{
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();

		let mut item: T = InitFrom::init_from(context.clone());

		// could rand shuffle if rand get imported later.
		let disordered = [
			[1u16,2,3,5,4],
			[2,5,1,3,4],
			[5,3,2,4,1],
		];
		for r in disordered.iter() {
			for i in r {
				let v: V = i.clone().into();
				let i: u32 = i.clone().into();
				item.set(v, &states.unchecked_latest_at(i).unwrap());
			}
			for i in r {
				let v: V = i.clone().into();
				let i: u32 = i.clone().into();
				assert_eq!(item.get_ref(&states.query_plan(i)), Some(&v));
			}
		}
	}


	fn test_set_get<T, V>(context: T::Context)
		where
			V: crate::historied::Value + std::fmt::Debug + From<u16> + Eq,
			T: InitFrom,
			T: crate::historied::DataBasis<S = ForkPlan<u32, u32>>,
			T: crate::historied::Data<V>,
			T: crate::historied::DataMut<
				V,
				Index = (u32, u32),
				SE = Latest<(u32, u32)>,
			>,
	{
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();

		let mut item: T = InitFrom::init_from(context.clone());

		for i in 0..6 {
			assert_eq!(item.get(&states.query_plan(i)), None);
		}

		// setting value respecting branch build order
		for i in 1..6 {
			item.set(i.into(), &states.unchecked_latest_at(i.into()).unwrap());
		}

		for i in 1..6 {
			assert_eq!(item.get(&states.query_plan(i.into())), Some(i.into()));
		}

		let ref_1 = states.query_plan(1u16.into());
		assert_eq!(Some(false), states.branch_state_mut(&1, |ls| ls.drop_state()));

		let ref_1_bis = states.query_plan(1);
		assert_eq!(item.get(&ref_1), Some(1.into()));
		assert_eq!(item.get(&ref_1_bis), None);
		item.set(11.into(), &states.unchecked_latest_at(1).unwrap());
		// lazy linear clean of drop state on insert
		assert_eq!(item.get(&ref_1), Some(11.into()));
		assert_eq!(item.get(&ref_1_bis), Some(11.into()));

		item = InitFrom::init_from(context.clone());

		// need fresh state as previous modification leaves unattached branches
		let mut states = test_states();
		// could rand shuffle if rand get imported later.
		let disordered = [
			[1u16,2,3,5,4],
			[2,5,1,3,4],
			[5,3,2,4,1],
		];
		for r in disordered.iter() {
			for i in r {
				let v: V = i.clone().into();
				let i: u32 = i.clone().into();
				item.set(v, &states.unchecked_latest_at(i).unwrap());
			}
			for i in r {
				let v: V = i.clone().into();
				let i: u32 = i.clone().into();
				assert_eq!(item.get(&states.query_plan(i)), Some(v));
			}
		}
	}

	#[cfg(not(feature = "force-data"))]
	fn test_force_set_get<T, V>(_context: T::Context) where
		T: crate::historied::DataMut<V>,
		V: crate::historied::Value,
	{ }

	#[cfg(feature = "force-data")]
	fn test_force_set_get<T, V>(context: T::Context)
		where
			V: crate::historied::Value + std::fmt::Debug + From<u16> + Eq,
			T: InitFrom,
			T: codec::Encode,
			T: DecodeWithContext,
			T: crate::Trigger,
			T: crate::historied::DataBasis<
				S = ForkPlan<u32, u32>,
				Index = (u32, u32),
			>,
			T: crate::historied::Data<V>,
			T: crate::historied::DataMut<
				V,
				SE = Latest<(u32, u32)>,
			>,
			T: crate::historied::force::ForceDataMut<V>,
	{
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _
		let mut states = test_states();
		let mut item: T = InitFrom::init_from(context.clone());

		for i in 0..6 {
			assert_eq!(item.get(&states.query_plan(i)), None);
		}

		// setting value not respecting branch build order
		assert_eq!(UpdateResult::Changed(()), item.force_set(0.into(), &(1, 2)));
		assert_eq!(UpdateResult::Changed(()), item.force_set(1.into(), &(1, 1)));
		// out of range
		assert_eq!(UpdateResult::Changed(()), item.force_set(8.into(), &(1, 0)));
		// can set in invalid range too
		assert_eq!(UpdateResult::Changed(()), item.force_set(3.into(), &(2, 5)));
		assert_eq!(UpdateResult::Changed(()), item.force_set(2.into(), &(2, 1)));

		let mut states2 = states.clone();

		let check = |states: &mut crate::management::tree::test::TestState, item: &T| {
			assert_eq!(item.get(&states.query_plan(1)), Some(0.into()));
			assert_eq!(item.get(&states.query_plan(2)), Some(2.into()));
		};
		check(&mut states, &item);

		if T::TRIGGER {
			// Using the item from fresh state
			// reqires trigger first
			item.trigger_flush();
		}

		let encoded = item.encode();
		let item = T::decode_with_context(&mut encoded.as_slice(), &context).unwrap();
		check(&mut states2, &item);
	}

	use ref_cast::RefCast;
	#[derive(RefCast)]
	#[repr(transparent)]
	#[derive(Clone, Copy, PartialEq, Eq, Debug)]
	/// U16 with 0 as neutral item.
	struct U16Neutral(u16); 

	impl std::ops::Deref for U16Neutral {
		type Target = u16;
		fn deref(&self) -> &u16 {
			&self.0
		}
	}

	impl std::ops::DerefMut for U16Neutral {
		fn deref_mut(&mut self) -> &mut u16 {
			&mut self.0
		}
	}

	impl From<u16> for U16Neutral {
		#[inline(always)]
		fn from(v: u16) -> Self {
			U16Neutral(v)
		}
	}

	impl Value for U16Neutral {
		const NEUTRAL: bool = true;

		type Storage = u16;

		#[inline(always)]
		fn is_neutral(&self) -> bool {
			self.0 == 0
		}

		#[inline(always)]
		fn is_storage_neutral(storage: &Self::Storage) -> bool {
			storage == &0u16
		}

		#[inline(always)]
		fn from_storage(storage: Self::Storage) -> Self {
			U16Neutral(storage)
		}

		#[inline(always)]
		fn into_storage(self) -> Self::Storage {
			self.0
		}
	}

	impl ValueRef for U16Neutral {
		fn from_storage_ref(storage: &Self::Storage) -> &Self {
			U16Neutral::ref_cast(storage)
		}

		fn into_storage_ref(&self) -> &Self::Storage {
			&self.0
		}

		fn from_storage_ref_mut(storage: &mut Self::Storage) -> &mut Self {
			U16Neutral::ref_cast_mut(storage)
		}

		fn into_storage_ref_mut(&mut self) -> &mut Self::Storage {
			&mut self.0
		}
	}

	fn test_migrate<T, V> (
		context1: T::Context,
		context2: T::Context,
		context3: T::Context,
		context4: T::Context,
	)	where
		V: crate::historied::Value + std::fmt::Debug + From<u16> + Eq,
		T: InitFrom + Trigger,
		T: Clone + codec::Encode + DecodeWithContext,
		T: TreeTestMethods,
		T: crate::historied::DataBasis<S = ForkPlan<u32, u32>>,
		T: crate::historied::Data<V>,
		T: crate::historied::DataMut<
			V,
			Index = (u32, u32),
			SE = Latest<(u32, u32)>,
			GC = MultipleGc<u32, u32>,
			Migrate = MultipleMigrate<u32, u32>,
		>,
	{
		use crate::management::{ManagementMut, Management, ForkableManagement};
		use crate::test::StateInput;

		let check_state = |states: &mut crate::test::InMemoryMgmtSer, target: Vec<(u32, u32)>| {
			let mut gc = states.get_migrate();
			let (pruning, iter) = gc.migrate().touched_state();
			assert_eq!(pruning, None);
			let mut set = std::collections::BTreeSet::new();
			for s in iter {
				set.insert(s.clone());
			}

			let reference: std::collections::BTreeSet<_> = target.into_iter().collect();
			assert_eq!(set, reference);
		};

		let mut states = crate::test::InMemoryMgmtSer::default();
		let s0 = states.latest_state_fork();

		let mut item1: T = InitFrom::init_from(context1.clone());
		let mut item2: T = InitFrom::init_from(context2.clone());
		let s1 = states.append_external_state(StateInput(1), &s0).unwrap();
		item1.set(1.into(), &states.get_db_state_mut(&StateInput(1)).unwrap());
		item2.set(1.into(), &states.get_db_state_mut(&StateInput(1)).unwrap());
		// fusing cano
		let _ = states.append_external_state(StateInput(101), s1.latest()).unwrap();
		item1.set(2.into(), &states.get_db_state_mut(&StateInput(101)).unwrap());
		item2.set(2.into(), &states.get_db_state_mut(&StateInput(101)).unwrap());
		let s1 = states.append_external_state(StateInput(102), s1.latest()).unwrap();
		item1.set(3.into(), &states.get_db_state_mut(&StateInput(102)).unwrap());
		let s1 = states.append_external_state(StateInput(103), s1.latest()).unwrap();
		item1.set(4.into(), &states.get_db_state_mut(&StateInput(103)).unwrap());
		let _ = states.append_external_state(StateInput(104), s1.latest()).unwrap();
		item1.set(5.into(), &states.get_db_state_mut(&StateInput(104)).unwrap());
		let s1 = states.append_external_state(StateInput(105), s1.latest()).unwrap();
		item1.set(6.into(), &states.get_db_state_mut(&StateInput(105)).unwrap());
		item2.set(6.into(), &states.get_db_state_mut(&StateInput(105)).unwrap());
		// end fusing (shift following branch index by 2)
		let _s2 = states.append_external_state(StateInput(2), &s0).unwrap();
		let s1b = states.append_external_state(StateInput(12), s1.latest()).unwrap();
		let s1 = states.append_external_state(StateInput(13), s1b.latest()).unwrap();
		let _sx = states.append_external_state(StateInput(14), s1.latest()).unwrap();

		let s3 = states.append_external_state(StateInput(3), s1.latest()).unwrap();
		let _s4 = states.append_external_state(StateInput(4), s1.latest()).unwrap();
		let _s5 = states.append_external_state(StateInput(5), s1b.latest()).unwrap();
		// 0> 1: _ _ X
		// |			 |> 3: 1
		// |			 |> 4: 1
		// |		 |> 5: 1
		// |> 2: _ _
		let mut item3: T = InitFrom::init_from(context3.clone());
		let mut item4: T = InitFrom::init_from(context4.clone());
		item1.set(15.into(), &states.get_db_state_mut(&StateInput(5)).unwrap());
		item2.set(15.into(), &states.get_db_state_mut(&StateInput(5)).unwrap());
		item1.set(12.into(), &states.get_db_state_mut(&StateInput(2)).unwrap());

		let s3head = states.append_external_state(StateInput(32), s3.latest()).unwrap();
		item1.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item2.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item3.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		item4.set(13.into(), &states.get_db_state_mut(&StateInput(32)).unwrap());
		let s3tmp = states.append_external_state(StateInput(33), s3head.latest()).unwrap();
		item1.set(14.into(), &states.get_db_state_mut(&StateInput(33)).unwrap());
		item3.set(0.into(), &states.get_db_state_mut(&StateInput(33)).unwrap());
		let s3head = states.append_external_state(StateInput(34), s3tmp.latest()).unwrap();
		let _s6 = states.append_external_state(StateInput(6), s3tmp.latest()).unwrap();
		let _s3head = states.append_external_state(StateInput(35), s3head.latest()).unwrap();
		item1.set(15.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item2.set(15.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item4.set(0.into(), &states.get_db_state_mut(&StateInput(35)).unwrap());
		item1.set(0.into(), &states.get_db_state_mut(&StateInput(6)).unwrap());

		// Apply change of composite to 33
		let filter_out = [101, 104, 14, 2, 4, 5];
		let mut filter_qp = vec![];
		// No dropped
		check_state(&mut states, filter_qp.clone());
		for i in filter_out.iter() {
			let qp = states.get_db_state(&StateInput(*i)).unwrap();
			filter_qp.push(qp.index());
		}

		let fp = states.get_db_state(&StateInput(35)).unwrap();
		states.canonicalize(fp, *s3tmp.latest(), None);
		// other drops from filter_out
		check_state(&mut states, filter_qp.clone());
		// no query plan for 14
		let filter_in = [1, 102, 103, 105, 12, 13, 32, 33, 34, 35, 6];

		let check_gc = |item1: &T, item2: &T, item3: &T, item4: &T, states: &mut crate::test::InMemoryMgmtSer| {
			//panic!("{:?} \n {:?}", old_state, states);
			let mut gc_item1 = item1.clone();
			let mut gc_item2 = item2.clone();
			let mut gc_item3 = item3.clone();
			let mut gc_item4 = item4.clone();
			{
				let gc = states.get_gc().unwrap();
				gc_item1.gc(gc.as_ref());
				gc_item2.gc(gc.as_ref());
				gc_item3.gc(gc.as_ref());
				gc_item4.gc(gc.as_ref());
				//panic!("{:?}", (gc.as_ref(), item4, gc_item4));
			}
			assert_eq!(gc_item1.nb_internal_history(), 8);
			assert_eq!(gc_item2.nb_internal_history(), 4);
			assert_eq!(gc_item3.nb_internal_history(), 2); // actually untouched
			assert_eq!(gc_item4.nb_internal_history(), 2); // actually untouched
			assert_eq!(gc_item1.nb_internal_branch(), 5);
			assert_eq!(gc_item2.nb_internal_branch(), 3);
			assert_eq!(gc_item3.nb_internal_branch(), 1);
			assert_eq!(gc_item4.nb_internal_branch(), 1);

			for i in filter_in.iter() {
				let fp = states.get_db_state(&StateInput(*i)).unwrap();
				assert_eq!(gc_item1.get(&fp), item1.get(&fp));
				assert_eq!(gc_item2.get(&fp), item2.get(&fp));
				assert_eq!(gc_item3.get(&fp), item3.get(&fp));
				assert_eq!(gc_item4.get(&fp), item4.get(&fp));
			}
			//panic!("{:?}", (gc, item1, gc_item1));
		};

		check_gc(&item1, &item2, &item3, &item4, &mut states.clone());
		item1.trigger_flush();
		let encoded = item1.encode();
		item1 = T::decode_with_context(&mut encoded.as_slice(), &context1).unwrap();
		item2.trigger_flush();
		let encoded = item2.encode();
		item2 = T::decode_with_context(&mut encoded.as_slice(), &context2).unwrap();
		item3.trigger_flush();
		let encoded = item3.encode();
		item3 = T::decode_with_context(&mut encoded.as_slice(), &context3).unwrap();
		item4.trigger_flush();
		let encoded = item4.encode();
		item4 = T::decode_with_context(&mut encoded.as_slice(), &context4).unwrap();
		check_gc(&item1, &item2, &item3, &item4, &mut states.clone());

		let check_migrate = |item1: &T, item2: &T, item3: &T, item4: &T, states: &mut crate::test::InMemoryMgmtSer| {
			let old_state = states.clone();
			// migrate 
			let filter_in = [33, 34, 35, 6];
			let mut gc_item1 = item1.clone();
			let mut gc_item2 = item2.clone();
			let mut gc_item3 = item3.clone();
			let mut gc_item4 = item4.clone();
			let mut states = states;
			{
				let mut gc = states.get_migrate();
				gc_item1.migrate(gc.migrate());
				gc_item2.migrate(gc.migrate());
				gc_item3.migrate(gc.migrate());
				gc_item4.migrate(gc.migrate());
				gc.applied_migrate();
			}
			// empty (applied_migrate ran)
			check_state(&mut states, vec![]);

			for i in filter_in.iter() {
				let fp = states.get_db_state(&StateInput(*i)).unwrap();
				assert_eq!(gc_item1.get(&fp), item1.get(&fp));
				assert_eq!(gc_item2.get(&fp), item2.get(&fp));
				assert_eq!(gc_item3.get(&fp), item3.get(&fp));
				assert_eq!(gc_item4.get(&fp), item4.get(&fp));
			}
			assert_eq!(gc_item1.nb_internal_history(), 8);
			assert_eq!(gc_item2.nb_internal_history(), 4);
			assert_eq!(gc_item3.nb_internal_history(), 2);
			assert_eq!(gc_item4.nb_internal_history(), 2);
			assert_eq!(gc_item1.nb_internal_branch(), 2);
			assert_eq!(gc_item2.nb_internal_branch(), 1);
			assert_eq!(gc_item3.nb_internal_branch(), 1);
			assert_eq!(gc_item4.nb_internal_branch(), 1);

			// on previous state set migrate with pruning_treshold 
			let filter_in = [33, 34, 35, 6];
			let mut gc_item1 = item1.clone();
			let mut gc_item2 = item2.clone();
			let mut gc_item3 = item3.clone();
			let mut gc_item4 = item4.clone();
			let mut states = old_state;
			let fp = states.get_db_state(&StateInput(35)).unwrap();
			states.canonicalize(fp, *s3tmp.latest(), Some(s3tmp.latest().1));
			{
				let mut gc = states.get_migrate();
				gc_item1.migrate(gc.migrate());
				gc_item2.migrate(gc.migrate());
				gc_item3.migrate(gc.migrate());
				gc_item4.migrate(gc.migrate());
				gc.applied_migrate();
				//panic!("{:?}", (gc, item3, gc_item3));
			}
			for i in filter_in.iter() {
				let fp = states.get_db_state(&StateInput(*i)).unwrap();
				assert_eq!(gc_item1.get(&fp), item1.get(&fp));
				assert_eq!(gc_item2.get(&fp), item2.get(&fp));
				if V::NEUTRAL {
					assert_eq!(gc_item3.get(&fp), None);
				} else {
					assert_eq!(gc_item3.get(&fp), item3.get(&fp));
				}
				assert_eq!(gc_item4.get(&fp), item4.get(&fp));
			}
			assert_eq!(gc_item1.nb_internal_history(), 3);
			assert_eq!(gc_item2.nb_internal_history(), 2);
			if V::NEUTRAL {
				assert_eq!(gc_item3.nb_internal_history(), 0);
			} else {
				assert_eq!(gc_item3.nb_internal_history(), 1);
			}
			assert_eq!(gc_item4.nb_internal_history(), 2);
			assert_eq!(gc_item1.nb_internal_branch(), 2);
			assert_eq!(gc_item2.nb_internal_branch(), 1);
			if V::NEUTRAL {
				assert_eq!(gc_item3.nb_internal_branch(), 0);
			} else {
				assert_eq!(gc_item3.nb_internal_branch(), 1);
			}
			assert_eq!(gc_item4.nb_internal_branch(), 1);
		};

		check_migrate(&item1, &item2, &item3, &item4, &mut states.clone());
		item1.trigger_flush();
		let encoded = item1.encode();
		item1 = T::decode_with_context(&mut encoded.as_slice(), &context1).unwrap();
		item2.trigger_flush();
		let encoded = item2.encode();
		item2 = T::decode_with_context(&mut encoded.as_slice(), &context2).unwrap();
		item3.trigger_flush();
		let encoded = item3.encode();
		item3 = T::decode_with_context(&mut encoded.as_slice(), &context3).unwrap();
		item4.trigger_flush();
		let encoded = item4.encode();
		item4 = T::decode_with_context(&mut encoded.as_slice(), &context4).unwrap();
		check_migrate(&item1, &item2, &item3, &item4, &mut states.clone());
	}

	#[test]
	fn test_memory_only() {
		type BD = crate::backend::in_memory::MemoryOnly<u32, u32>;
		type D = crate::backend::in_memory::MemoryOnly<
			crate::historied::linear::Linear<u32, u32, BD>,
			u32,
		>;
		type Tree = super::Tree<u32, u32, u32, D, BD>;
		test_set_get::<Tree, u32>(((), ()));
		test_set_get_ref::<Tree, u32>(((), ()));
		test_migrate::<Tree, u32>(((), ()), ((), ()), ((), ()), ((), ()));
		test_force_set_get::<Tree, u32>(((), ()));
	}

	macro_rules! test_with_trigger_inner {
		($meta: ty) => {{
		use crate::backend::nodes::{Head, ContextHead, InMemoryNoThreadBackend};
		use crate::backend::in_memory::MemoryOnly;

		type M = $meta;
		type Value = u16;
		type MemOnly = MemoryOnly<Value, u32>;
		type Backend1 = InMemoryNoThreadBackend::<Value, u32, MemOnly, M>;
		type BD = Head<Value, u32, MemOnly, M, Backend1, ()>;

		type V2 = crate::historied::linear::Linear<Value, u32, BD>;
		type MemOnly2 = MemoryOnly<V2, u32>;
		type Backend2 = InMemoryNoThreadBackend::<V2, u32, MemOnly2, M>;
		type D = Head<V2, u32, MemOnly2, M, Backend2, ContextHead<Backend1, ()>>;
		let backend1 = Backend1::new();
		let init_head_child = ContextHead {
			backend: backend1.clone(),
			key: b"any".to_vec(),
			node_init_from: (),
			encoded_indexes: Vec::new(),
		};
		let backend2 = Backend2::new();
		let init_head = ContextHead {
			backend: backend2.clone(),
			key: b"any".to_vec(),
			node_init_from: init_head_child.clone(),
			encoded_indexes: Vec::new(),
		};
		type Tree = super::Tree<u32, u32, Value, D, BD>;
		let context1 = (init_head, init_head_child);
		let mut context2 = context1.clone();
		context2.0.key = b"other".to_vec();
		context2.1.key = context2.0.key.clone();
		context2.0.node_init_from = context2.1.clone();
		let mut context3 = context1.clone();
		context3.0.key = b"othe3".to_vec();
		context3.1.key = context3.0.key.clone();
		context3.0.node_init_from = context3.1.clone();
		let mut context4 = context1.clone();
		context4.0.key = b"othe4".to_vec();
		context4.1.key = context4.0.key.clone();
		context4.0.node_init_from = context4.1.clone();

		test_set_get::<Tree, u16>(context1.clone());
		// trigger flush test is into test_migrate
		test_migrate::<Tree, u16>(context1.clone(), context2.clone(), context3.clone(), context4.clone());
		test_force_set_get::<Tree, u16>(context1.clone());
	}}}

	#[test]
	fn test_with_trigger() {
		test_with_trigger_inner!(crate::backend::nodes::test::MetaNb1);
		test_with_trigger_inner!(crate::backend::nodes::test::MetaNb2);
		test_with_trigger_inner!(crate::backend::nodes::test::MetaNb3);
	}
}
