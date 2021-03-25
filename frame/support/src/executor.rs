// This file is part of Substrate.
// Copyright (C) 2021 Parity Technologies (UK) Ltd.

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

use sp_std::prelude::*;
use crate::{weights::Weight, traits::Get};
use codec::{Encode, Decode};
use sp_runtime::traits::Zero;
use crate::{RuntimeDebugNoBound, PartialEqNoBound, EqNoBound, CloneNoBound};

const LOG_TARGET: &'static str = "runtime::task_executor";

/// A task that can be stored in storage and executed at some later time.
///
/// This trait itself does not make any assumptions about *when* the task is executed. As far as
/// this trait is concerned, it can be now, all at once. It can be executed as mandatory work in
/// `on_initialize` or `on_finalize`, or in some other low priority circumstance (e.g. on_idle).
///
/// If the type implementing this trait is generic over `<T: Config>` then one needs to derive
/// [`CloneNoBound`], [`PartialEqNoBound`], [`EqNoBound`], [`RuntimeDebugNoBound`], as opposed to
/// their normal counterparts, and implement `Default` manually. This is to prevent `T` to be
/// bounded to these traits.
pub trait RuntimeTask:
	Sized + Clone + Default + Encode + Decode + PartialEq + Eq + sp_std::fmt::Debug
{
	/// Execute the task while consuming self. The task must not most consume more than `max_weight`
	/// under any circumstance. Consuming *less* than `max_weight` is allowed.
	///
	/// A tuple is returned, where the items are as follows:
	///   1. Option<Self>, where `None` means that this task is now complete (and shall not be kept
	///      in storage anymore), and `Some(_)` indicating that this task is not yet complete, and
	///      should be executed at a later time.
	///   2. The actual amount of weight that was consumed. Must always be less than `max_weight`.
	///      parameter.
	///
	/// It is critically important for a task to only return a non-zero consumed weight **ONLY if it
	/// _actually did something_**. If a positive weight is returned, then an executor could
	/// interpret this as a task that could use another execution slot, and continue the execution
	/// potentially for numerous iterations.
	fn execute(self, max_weight: Weight) -> (Option<Self>, Weight);

	/// The leftover weight that this task expects to execute, if any.
	#[cfg(test)]
	fn leftover(&self) -> Weight;
}

#[cfg(any(test, feature = "std"))]
impl RuntimeTask for () {
	fn execute(self, _: Weight) -> (Option<Self>, Weight) {
		(None, 0)
	}
	#[cfg(test)]
	fn leftover(&self) -> Weight {
		0
	}
}

/// Common trait for a executor that is stored as a storage item.
pub trait StoredExecutor {
	/// The task type used by this executor.
	type Task: RuntimeTask;

	/// Something that can define how much weight quote this executor is allowed to use per
	/// execution.
	type Quota: Get<Weight>;

	/// Execute all tasks based on an unspecified strategy, consuming at most `Self::Quota` and
	/// returning the actual amount of weight consumed.
	///
	/// The returned weight must take into account the cost of internal operations of the
	/// implementation, such as scheduling, as well. But, it DOES NOT take into account any
	/// potential storage operations that needed to be performed to fetch `Self` from storage.
	///
	/// A  sensible patter of using an implementation of this trait is therefore:
	///
	/// ```ignore
	/// let mut consumed = <StorageItemExecutor<T>>::mutate(|e| e.execute());
	/// consumed += <weight of 1 read and write for the mutate call above>;
	/// ```
	// TODO: while the work that this does itself is pretty negligible, must benchmark it anyhow and
	// take it into account.
	fn execute(&mut self) -> Weight;

	/// Create a new (empty) instance of [`Self`].
	fn new() -> Self;

	/// Add a new task to the internal state.
	fn add_task(&mut self, task: Self::Task);

	/// Remove all tasks, without executing any of them.
	fn clear(&mut self);

	/// Removes the first task that is equal to `task`.
	fn remove(&mut self, task: Self::Task);

	/// Returns the number of current tasks.
	fn count(&self) -> usize;

	/// Return a vector of all tasks.
	#[cfg(any(test, feature = "std"))]
	fn tasks(&self) -> Vec<Self::Task>;
	// TODO: providing an iter() might also be good.
}

#[cfg(any(test, feature = "std"))]
impl StoredExecutor for () {
	type Task = ();
	type Quota = ();

	fn execute(&mut self) -> Weight {
		unreachable!()
	}
	fn new() -> Self {
		unreachable!()
	}
	fn add_task(&mut self, _: Self::Task) {
		unreachable!()
	}
	fn clear(&mut self) {
		unreachable!()
	}
	fn remove(&mut self, _: Self::Task) {
		unreachable!()
	}
	fn count(&self) -> usize {
		unreachable!()
	}
	fn tasks(&self) -> Vec<Self::Task> {
		unreachable!()
	}
}

/// An executor that tries to execute as many tasks as possible in multiple passes over all of them.
///
/// A user may create an instance of this struct, add tasks to it (each of which must implement
///	[`RuntimeTask`]), place it in storage, and execute tasks via the [`execute`] method.
///
/// This executor is opinionated, and cane be potentially re-implemented with different strategies.
/// Namely, the assumption is that tasks are heterogenous, meaning that each might require different
/// weight or be in different stage of execution. See [`execute`] for more info.
///
/// From the tasks being heterogenous follows that if they are being iterated and one of them
/// fails to finish (i.e. return `Some(_)` in [`RuntimeTask::execute`]), we do **not** assume
/// that the rest of the tasks will also fail. Therefore, we always make a full
/// pass over the tasks, to make sure any of them can use any leftover weight. Once is a pass is
/// done without any of the tasks consuming any weight, then we conclude that this execution is
/// done.
///
/// # WARNING
///
/// This implementation is prone to the _weight leaking_ explained in [`RuntimeTask::execute`].
/// Namely, if a task keep consuming a little amount of weight in each execution, this executor will
/// assume that it still has work to do, and will indefinitely executor a second pass for it.
#[derive(Encode, Decode, RuntimeDebugNoBound, PartialEqNoBound, EqNoBound, CloneNoBound)]
pub struct MultiPassExecutor<Task: RuntimeTask, Quota: Get<Weight> = ()> {
	/// The queue of tasks.
	pub(crate) tasks: Vec<Task>,
	_marker: sp_std::marker::PhantomData<Quota>,
}

// TODO: can't we just have a DefaultNoBound as well? then we can ditch this.
impl<Task: RuntimeTask, Quota: Get<Weight>> Default for MultiPassExecutor<Task, Quota> {
	fn default() -> Self {
		Self { tasks: vec![], _marker: sp_std::marker::PhantomData }
	}
}

impl<Task: RuntimeTask, Quota: Get<Weight>> StoredExecutor for MultiPassExecutor<Task, Quota> {
	type Task = Task;
	type Quota = Quota;

	fn new() -> Self {
		Self { tasks: vec![], _marker: Default::default() }
	}

	fn add_task(&mut self, task: Task) {
		self.tasks.push(task)
	}

	fn clear(&mut self) {
		self.tasks.clear()
	}

	fn remove(&mut self, task: Task) {
		let maybe_index = self.tasks.iter().position(|t| t == &task);
		if let Some(index) = maybe_index {
			self.tasks.remove(index);
		}
	}

	fn count(&self) -> usize {
		self.tasks.len()
	}

	#[cfg(any(test, feature = "std"))]
	fn tasks(&self) -> Vec<Task> {
		self.tasks.clone()
	}

	fn execute(&mut self) -> Weight {
		let max_weight = Self::Quota::get();
		// NOTE: we can optimize this a bit: if we make a pass and 8/10 of the tasks do nothing, we
		// should mark them and not re-execute them in the next pass. Need to store Vec<(Task,
		// bool)> for this.
		if max_weight.is_zero() {
			return 0;
		}

		let mut leftover_weight = max_weight;
		loop {
			let (next_tasks, consumed) = single_pass::<Task>(self.tasks.as_ref(), leftover_weight);
			self.tasks = next_tasks;
			leftover_weight = leftover_weight.saturating_sub(consumed);

			if leftover_weight.is_zero() || consumed.is_zero() {
				// if we run out, or there's nothing to consume the weight, we're done.
				break;
			}
		}

		max_weight.saturating_sub(leftover_weight)
	}
}

/// An executor that only tries to execute a single pass on a given list of tasks in each
/// execution.
///
/// This is a much more conservative variation of the [`MultiPassExecutor`], and arguable more
/// suitable for homogenous tasks.
#[derive(Encode, Decode, RuntimeDebugNoBound, PartialEqNoBound, EqNoBound, CloneNoBound)]
pub struct SinglePassExecutor<Task: RuntimeTask, Quota: Get<Weight> = ()> {
	/// The queue of tasks.
	pub(crate) tasks: Vec<Task>,
	_marker: sp_std::marker::PhantomData<Quota>,
}

impl<Task: RuntimeTask, Quota: Get<Weight>> Default for SinglePassExecutor<Task, Quota> {
	fn default() -> Self {
		Self { tasks: vec![], _marker: sp_std::marker::PhantomData }
	}
}

impl<Task: RuntimeTask, Quota: Get<Weight>> StoredExecutor for SinglePassExecutor<Task, Quota> {
	type Task = Task;
	type Quota = Quota;

	fn new() -> Self {
		Self { tasks: vec![], _marker: Default::default() }
	}

	fn add_task(&mut self, task: Task) {
		self.tasks.push(task)
	}

	fn clear(&mut self) {
		self.tasks.clear()
	}

	fn remove(&mut self, task: Task) {
		let maybe_index = self.tasks.iter().position(|t| t == &task);
		if let Some(index) = maybe_index {
			self.tasks.remove(index);
		}
	}

	fn count(&self) -> usize {
		self.tasks.len()
	}

	#[cfg(any(test, feature = "std"))]
	fn tasks(&self) -> Vec<Task> {
		self.tasks.clone()
	}

	fn execute(&mut self) -> Weight {
		let max_weight = Self::Quota::get();
		let (next_tasks, consumed) = single_pass::<Task>(self.tasks.as_ref(), max_weight);
		self.tasks = next_tasks;
		consumed
	}
}

/// Make a single pass over some tasks, returning a new set of tasks that remain un-finished, along
/// the consumed weight.
///
/// This is useful for different scheduling strategies.
pub(crate) fn single_pass<T: RuntimeTask>(tasks: &[T], max_weight: Weight) -> (Vec<T>, Weight) {
	// just a tiny optimization for this edge case
	if tasks.is_empty() || max_weight.is_zero() {
		return (tasks.to_vec(), Zero::zero());
	}

	let mut leftover_weight = max_weight;
	let next_tasks = tasks
		.iter()
		.cloned()
		.filter_map(|task| {
			if leftover_weight.is_zero() {
				return Some(task);
			}

			let (maybe_leftover_task, consumed) = task.execute(leftover_weight);
			leftover_weight = leftover_weight.saturating_sub(consumed);
			maybe_leftover_task
		})
		.collect::<Vec<_>>();

	log::debug!(
		target: LOG_TARGET,
		"executed a single pass.\nPrev tasks = {:?}\nNext tasks = {:?}",
		tasks,
		next_tasks,
	);

	(next_tasks, max_weight.saturating_sub(leftover_weight))
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Clone, Encode, Decode, Default, PartialEq, Eq, Debug)]
	struct Task {
		weight: Weight,
		half: u8,
		greedy: bool,
	}

	struct TaskBuilder {
		half: u8,
		greedy: bool,
	}

	impl Default for TaskBuilder {
		fn default() -> Self {
			Self { half: 0, greedy: true }
		}
	}

	impl TaskBuilder {
		fn half(mut self, half: u8) -> Self {
			self.half = half;
			self
		}

		fn greedy(mut self, greedy: bool) -> Self {
			self.greedy = greedy;
			self
		}

		fn build(self, weight: Weight) -> Task {
			Task { weight, greedy: self.greedy, half: self.half }
		}
	}

	impl Task {
		/// Should be called after `self.weight` has been reduce to reflect the update of an
		/// execution, to determine of this task should live or not.
		fn maybe_destroy(self) -> Option<Self> {
			if self.weight > 0 {
				Some(self)
			} else {
				None
			}
		}

		/// Should consume `amount` of `Self`'s weight, capping it at `max_weight`.
		fn consume(mut self, amount: Weight, max_weight: Weight) -> (Option<Self>, Weight) {
			println!("Consuming {:?} with {} from {}", &self, amount, max_weight);
			let consumed = if self.greedy {
				if amount > max_weight {
					// we are greedy and we need more than max_weight, consume all of it.
					self.weight -= max_weight;
					max_weight
				} else {
					// we are greedy and max_weight is enough. Destroy self.
					self.weight -= amount;
					amount
				}
			} else {
				if amount > max_weight {
					// we are not greedy and max_weight is not enough, thus noop.
					0
				} else {
					// we are not greedy and max_weight is enough, thus destroy self.
					self.weight -= amount;
					amount
				}
			};

			(self.maybe_destroy(), consumed)
		}
	}

	impl RuntimeTask for Task {
		fn execute(mut self, max_weight: Weight) -> (Option<Self>, Weight) {
			println!("++ Execute {:?} by {}", &self, max_weight);
			let weight_needed = self.weight;
			match self.half {
				0 => {
					// at this point we try and consume as much as possible.
					self.consume(weight_needed, max_weight)
				}
				_ => {
					// try and consume either half of your needed weight, or all of the available,
					// if it is less.
					self.half -= 1;
					self.consume(weight_needed / 2, max_weight)
				}
			}
		}

		fn leftover(&self) -> Weight {
			self.weight
		}
	}

	fn remaining_weights_of<T: RuntimeTask, E: StoredExecutor<Task = T>>(
		executor: &E,
	) -> Vec<Weight> {
		executor.tasks().iter().map(|t| t.leftover()).collect::<Vec<_>>()
	}

	frame_support::parameter_types! {
		static Quota: Weight = 10;
	}

	#[test]
	fn single_pass_less_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		Quota::set(7);
		let mut executor = SinglePassExecutor::<Task, Quota>::new();
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);

		assert_eq!(executor.execute(), 7);
		assert_eq!(remaining_weights_of(&executor), vec![3, 10, 10]);

		assert_eq!(executor.execute(), 7);
		assert_eq!(remaining_weights_of(&executor), vec![6, 10]);

		assert_eq!(executor.execute(), 7);
		assert_eq!(remaining_weights_of(&executor), vec![9]);

		assert_eq!(executor.execute(), 7);
		assert_eq!(remaining_weights_of(&executor), vec![2]);

		assert_eq!(executor.execute(), 2);
		assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());

		// noop
		assert_eq!(executor.execute(), 0);
	}

	#[test]
	fn single_pass_more_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut executor = SinglePassExecutor::<Task, Quota>::new();
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);

		Quota::set(12);
		assert_eq!(executor.execute(), 12);
		assert_eq!(remaining_weights_of(&executor), vec![8, 10]);

		assert_eq!(executor.execute(), 12);
		assert_eq!(remaining_weights_of(&executor), vec![6]);

		assert_eq!(executor.execute(), 6);
		assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());

		// noop
		assert_eq!(executor.execute(), 0);
	}

	#[test]
	fn single_pass_equal_weight_to_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut executor = SinglePassExecutor::<Task, Quota>::new();
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		executor.add_task(TaskBuilder::default().build(10));
		assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);

		Quota::set(10);
		assert_eq!(executor.execute(), 10);
		assert_eq!(remaining_weights_of(&executor), vec![10, 10]);

		assert_eq!(executor.execute(), 10);
		assert_eq!(remaining_weights_of(&executor), vec![10]);

		assert_eq!(executor.execute(), 10);
		assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());

		// noop
		assert_eq!(executor.execute(), 0);
	}

	#[test]
	fn multi_pass_execution_basic() {
		// equal
		{
			let mut executor = MultiPassExecutor::<Task, Quota>::new();
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));

			Quota::set(30);
			executor.execute();
			assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());
		}

		// more
		{
			let mut executor = MultiPassExecutor::<Task, Quota>::new();
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));

			Quota::set(33);
			executor.execute();
			assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());
		}

		// less
		{
			let mut executor = MultiPassExecutor::<Task, Quota>::new();
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));

			Quota::set(27);
			executor.execute();
			assert_eq!(remaining_weights_of(&executor), vec![3]);
		}
	}

	#[test]
	fn multi_step_simple() {
		let _ = env_logger::try_init();
		let mut executor = MultiPassExecutor::<Task, Quota>::new();
		executor.add_task(TaskBuilder::default().half(1).build(10));
		executor.add_task(TaskBuilder::default().half(1).build(10));
		executor.add_task(TaskBuilder::default().half(1).build(10));

		// first, each task will eat up 5, 15 in total. Then, one of them drains the last 2.
		Quota::set(17);
		assert_eq!(executor.execute(), 17);
		assert_eq!(remaining_weights_of(&executor), vec![3, 5, 5]);
	}

	#[test]
	fn multi_step_where_additional_pass_is_useful() {
		let _ = env_logger::try_init();
		let mut executor = MultiPassExecutor::<Task, Quota>::new();
		executor.add_task(TaskBuilder::default().half(1).greedy(false).build(30));
		executor.add_task(TaskBuilder::default().half(1).greedy(false).build(20));
		executor.add_task(TaskBuilder::default().half(1).greedy(false).build(10));

		// first batch, we consume 15 + 10 + 5 = 30. Second round, only the last one can use the
		// remaining 5. 1 unit is unused.
		Quota::set(36);
		assert_eq!(executor.execute(), 35);
		assert_eq!(remaining_weights_of(&executor), vec![15, 10]);
	}

	#[test]
	fn empty_executor_is_noop() {
		fn with_executor<E: StoredExecutor<Task = Task>>(mut executor: E) {
			assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());

			Quota::set(0);
			assert_eq!(executor.execute(), 0);
			assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());

			assert_eq!(executor.execute(), 0);
			assert_eq!(remaining_weights_of(&executor), Vec::<Weight>::new());
		}

		with_executor(MultiPassExecutor::<Task, Quota>::new());
		with_executor(SinglePassExecutor::<Task, Quota>::new());
	}

	#[test]
	fn no_weight_allowed_is_noop() {
		fn with_executor<E: StoredExecutor<Task = Task>>(mut executor: E) {
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));
			executor.add_task(TaskBuilder::default().build(10));
			assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);

			Quota::set(0);
			assert_eq!(executor.execute(), 0);
			assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);

			assert_eq!(executor.execute(), 0);
			assert_eq!(remaining_weights_of(&executor), vec![10, 10, 10]);
		}

		with_executor(MultiPassExecutor::<Task, Quota>::new());
		with_executor(SinglePassExecutor::<Task, Quota>::new());
	}
}
