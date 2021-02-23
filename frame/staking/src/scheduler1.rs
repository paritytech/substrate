use frame_support::weights::Weight;
use sp_runtime::traits::Zero;
use sp_runtime::RuntimeDebug;

pub trait TaskExecution<Task> {
	fn execute(task: Task, max_weight: Weight) -> (Option<Task>, Weight);
}

pub struct TaskExecutor;
impl TaskExecutor {
	pub fn execute<Task: Clone, E: TaskExecution<Task>>(tasks: &mut Vec<Task>, max_weight: Weight) -> Weight {
		// just a tiny optimization for this edge case
		if tasks.is_empty() || max_weight.is_zero() {
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

		let next_tasks = tasks.iter().cloned().filter_map(|task| {
			if leftover_weight.is_zero() {
				return Some(task)
			}

			let (maybe_leftover_task, consumed_weight) = E::execute(task, leftover_weight);
			leftover_weight = leftover_weight.saturating_sub(consumed_weight);
			maybe_leftover_task
		}).collect::<Vec<_>>();

		*tasks = next_tasks;
		max_weight.saturating_sub(leftover_weight)
	}
}
