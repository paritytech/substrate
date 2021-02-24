// TODO: move this to frame/support/scheduler.rs

use sp_std::prelude::*;
use frame_support::weights::Weight;
use codec::{Encode, Decode};
use sp_runtime::traits::Zero;
use sp_runtime::RuntimeDebug;

/// Definition of task within the runtime.
///
/// Each task is represented by something that implements this trait, and that certain something
/// needs be placed in storage for future scheduling. Therefore, it is required for the task type to
/// be `Encode + Decode + Default`.
// TODO: document that you might need to implement some stuff manually here, if you want to be
// generic over `T`.
pub trait RuntimeTask: Sized + Clone + Default + Encode + Decode {
	/// Execute the task while consuming self. The task may at most consume `max_weight` units of
	/// weight, but could potentially be less.
	///
	/// A tuple is returned, where the items are as follows:
	///   1. Option<Self>, where `None` means that this task is now complete (and shall not be kept
	///      in storage anymore), and `Some(_)` indicating that this task is not yet complete.
	///   2. The actual amount of weight that was consumed. Must always be less than `max_weight`.
	///      parameter.
	///
	/// It is critically important for a task to only return a positive consumed weight if it
	/// _actually did something_. If a positive weight is returned, then a scheduler could interpret
	/// this as a task that could use another execution slot, and continue the execution potentially
	/// for numerous iterations.
	fn execute(self, max_weight: Weight) -> (Option<Self>, Weight);
}

/// A wrapper for grouping storage-stored tasks together and executing them with a max weight.
///
/// A user may create an instance of this struct, add tasks to it (each of which must implement
///	[`RuntimeTask`]), place it in storage, and execute tasks via the [`execute`] method.
///
/// This scheduler is slightly opinionated, and cane be potentially re-implemented with different
/// strategies. Namely, the assumption is that tasks are heterogenous, meaning that each might
/// require different weight or be in different stage of execution. See [`execute`] for more info.
#[derive(Encode, Decode, Default, RuntimeDebug)]
pub struct RuntimeTaskScheduler<Task: RuntimeTask> {
	/// The queue of tasks.
	pub(crate) tasks: Vec<Task>
}

impl<Task: RuntimeTask> RuntimeTaskScheduler<Task> {
	/// Create a new (empty) instance of [`RuntimeTaskScheduler`].
	pub fn new() -> Self {
		Self { tasks: vec![] }
	}

	/// Add a new task to the internal queue.
	pub fn add_task(&mut self, task: Task) {
		self.tasks.push(task)
	}

	/// Remove all tasks.
	///
	/// # Warning
	///
	/// Does not attempt to execute any of the tasks!
	pub fn clear(&mut self) {
		self.tasks.clear()
	}

	/// Remove a single task.
	///
	/// # Panics
	///
	/// Panics if index is larger than the [`len`] of the scheduler's queue.
	pub fn remove(&mut self, index: usize) {
		self.tasks.remove(index);
	}

	/// Returns the number of current tasks.
	pub fn count(&self) -> usize {
		self.tasks.len()
	}

	/// Start executing [`Self::tasks`] in a first-come-first-serve manner, consuming at most
	/// `max_weight`.
	///
	/// This implementation assumes that tasks are heterogenous, meaning that if they are being
	/// iterated and once of them fails to finish (i.e. return `Some(_)` in
	/// [`RuntimeTask::execute`]), we do not assume that the rest of the tasks will also fail.
	/// Therefore, we always make a full pass over the tasks, to make sure any of them can use any
	/// leftover weight.
	// TODO: I assume here that the work that this code is doing itself consumes ZERO weight, which
	// is not correct.
	pub fn execute(&mut self, max_weight: Weight) -> Weight {
		let mut leftover_weight = max_weight;
		loop {
			let consumed = self.single_pass(leftover_weight);
			leftover_weight = leftover_weight.saturating_sub(consumed);

			if leftover_weight.is_zero() || consumed.is_zero() {
				// if we run out, or there's nothing to consume the weight, we're done.
				break;
			}
		}

		max_weight.saturating_sub(leftover_weight)
	}

	/// Make a single pass over all tasks, mutating self and removing done tasks along the way.
	pub(crate) fn single_pass(&mut self, max_weight: Weight) -> Weight {
		// just a tiny optimization for this edge case
		if self.tasks.is_empty() || max_weight.is_zero() {
			return Zero::zero()
		}

		// to be easily executed in a runtime storage mutate call.
		let mut leftover_weight = max_weight;

		// We take an approach which is more fair, but needs to consume a few more cycles: we
		// iterate over all tasks in each execution. Even if while executing task `t` we ran out of
		// resources, as long as there are any leftover weight, some of the upcoming tasks might be
		// able to consume that. This is pointless if tasks are homogenous, nonetheless we can't
		// make that assumption. Only assumption is that no task needs to consume `0` weight, for in
		// this case it wouldn't have been delegated to the scheduler in the first place.

		let next_tasks = self.tasks.iter().cloned().filter_map(|task| {
			if leftover_weight.is_zero() {
				return Some(task)
			}

			let (maybe_leftover_task, consumed_weight) = task.execute(leftover_weight);
			leftover_weight = leftover_weight.saturating_sub(consumed_weight);
			maybe_leftover_task
		}).collect::<Vec<_>>();

		self.tasks = next_tasks;
		max_weight.saturating_sub(leftover_weight)
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[derive(Clone, Encode, Decode, Default)]
	struct SimpleTask(Weight);

	impl RuntimeTask for SimpleTask {
		fn execute(mut self, max_weight: Weight) -> (Option<Self>, Weight) {
			if self.0 > max_weight {
				self.0 -= max_weight;
				(Some(self), max_weight)
			} else {
				(None, self.0)
			}
		}
	}

	fn remaining_weights_of(scheduler: &RuntimeTaskScheduler<SimpleTask>) -> Vec<Weight> {
		scheduler.tasks.iter().map(|t| t.0).collect::<Vec<_>>()
	}

	#[test]
	fn single_pass_less_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.single_pass(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![3, 10, 10]);

		assert_eq!(scheduler.single_pass(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![6, 10]);

		assert_eq!(scheduler.single_pass(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![9]);

		assert_eq!(scheduler.single_pass(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![2]);

		assert_eq!(scheduler.single_pass(7), 2);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.single_pass(7), 0);
	}

	#[test]
	fn single_pass_more_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.single_pass(12), 12);
		assert_eq!(remaining_weights_of(&scheduler), vec![8, 10]);

		assert_eq!(scheduler.single_pass(12), 12);
		assert_eq!(remaining_weights_of(&scheduler), vec![6]);

		assert_eq!(scheduler.single_pass(12), 6);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.single_pass(12), 0);
	}

	#[test]
	fn single_pass_equal_weight_to_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.single_pass(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10]);

		assert_eq!(scheduler.single_pass(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), vec![10]);

		assert_eq!(scheduler.single_pass(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.single_pass(10), 0);
	}

	#[test]
	fn batch_execution_basic() {
		// equal
		{
			let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));

			scheduler.execute(30);
			assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());
		}

		// more
		{
			let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));

			scheduler.execute(33);
			assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());
		}

		// less
		{
			let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));
			scheduler.add_task(SimpleTask(10));

			scheduler.execute(27);
			assert_eq!(remaining_weights_of(&scheduler), vec![3]);
		}
	}

	#[test]
	fn empty_scheduler_is_noop() {
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		scheduler.execute(10);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		scheduler.execute(20);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());
	}

	#[test]
	fn no_weight_allowed_is_noop() {
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		scheduler.execute(0);
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		scheduler.execute(0);
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);
	}
}
