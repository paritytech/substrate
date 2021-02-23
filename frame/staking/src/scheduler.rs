// TODO: move this to frame/support/scheduler.rs

use frame_support::weights::Weight;
use codec::{Encode, Decode};
use sp_runtime::traits::Zero;
use sp_runtime::RuntimeDebug;


#[derive(Encode, Decode, Default)]
pub struct RuntimeProxyObject<T: frame_system::Config>(sp_std::marker::PhantomData<T>);

/// Definition of task within the runtime. This is the thing that goes into storage.
pub trait RuntimeTask: Sized + Clone + Encode + Default {
	/// (None, consumed_weight) if task is done,
	/// (Some(_), consumed_weight) if task needs more weight, .
	fn execute(self, max_weight: Weight) -> (Option<Self>, Weight);
}

/// Each pallet would put this in their storage. Add a task to it upon demand.
#[derive(Encode, Decode, Default, RuntimeDebug)]
pub struct RuntimeTaskScheduler<Task: RuntimeTask> {
	pub(crate) tasks: Vec<Task>
}

impl<Task: RuntimeTask> RuntimeTaskScheduler<Task> {
	pub fn new() -> Self {
		Self { tasks: vec![] }
	}

	fn add_task(&mut self, task: Task) {
		self.tasks.push(task)
	}

	// returns the actual weight consumed.
	fn execute(&mut self, max_weight: Weight) -> Weight {
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

	#[derive(Clone, Encode)]
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
	fn less_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.execute(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![3, 10, 10]);

		assert_eq!(scheduler.execute(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![6, 10]);

		assert_eq!(scheduler.execute(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![9]);

		assert_eq!(scheduler.execute(7), 7);
		assert_eq!(remaining_weights_of(&scheduler), vec![2]);

		assert_eq!(scheduler.execute(7), 2);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.execute(7), 0);
	}

	#[test]
	fn more_weight_than_than_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.execute(12), 12);
		assert_eq!(remaining_weights_of(&scheduler), vec![8, 10]);

		assert_eq!(scheduler.execute(12), 12);
		assert_eq!(remaining_weights_of(&scheduler), vec![6]);

		assert_eq!(scheduler.execute(12), 6);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.execute(12), 0);
	}

	#[test]
	fn equal_weight_to_single_task() {
		// execute a series of tasks with less weight per block for single task.
		let mut scheduler = RuntimeTaskScheduler::<SimpleTask>::new();
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		scheduler.add_task(SimpleTask(10));
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10, 10]);

		assert_eq!(scheduler.execute(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), vec![10, 10]);

		assert_eq!(scheduler.execute(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), vec![10]);

		assert_eq!(scheduler.execute(10), 10);
		assert_eq!(remaining_weights_of(&scheduler), Vec::<Weight>::new());

		// noop
		assert_eq!(scheduler.execute(10), 0);
	}
}
