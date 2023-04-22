#![cfg_attr(not(feature = "std"), no_std)]

/// Edit this file to define custom logic or remove it if it is not needed.
/// Learn more about FRAME and the core library of Substrate FRAME pallets:
/// <https://docs.substrate.io/reference/frame-pallets/>
pub use pallet::*;

#[cfg(test)]
mod mock;

#[cfg(test)]
mod tests;

#[cfg(feature = "runtime-benchmarks")]
mod benchmarking;

#[frame_support::pallet(dev_mode)]
pub mod pallet {
	use codec::Codec;
	use frame_support::{
		dispatch::{Dispatchable, GetDispatchInfo},
		pallet_prelude::*,
		traits::{OnRuntimeUpgrade, UnfilteredDispatchable},
	};
	use frame_system::pallet_prelude::*;
	use sp_runtime::traits::Zero;

	/// How a task is being scheduled.
	enum Scheduling {
		/// Schedule to execute `on_idle`, while consuming at most `Weight`.
		OnIdle(Weight),
		/// Schedule to execute `on_initialize`, while consuming at most `Weight`.
		OnInitialize(Weight),
		/// Schedule to execute on `poll`, while consuming at most `Weight`.
		Poll(Weight),
		/// Scheduled to execute dispatching.
		///
		/// This could be through an extrinsic provided by a substrate offchain worker, or a normal
		/// bot running outside of the chian.
		Dispatch,
	}

	impl Scheduling {
		fn max_weight(&self) {
			match self {
				Scheduling::OnIdle(w) => w,
				Scheduling::OnInitialize(w) => w,
				Scheduling::Poll(w) => w,
				Scheduling::Dispatch => frame_support::traits::Bounded::max_value(),
			}
		}

		fn can_run(&self, requested_weight: Weight) -> bool {
			let allowed_weight = self.max_weight();
			requested_weight <= allowed_weight
		}
	}

	/// A task that is stored onchain.
	trait Task: Codec {
		/// Run the task, consuming self.
		///
		/// Returns the final consumed weight, and optionally the task itself, if it is not "over".
		/// Returning `None` implies the task is "over".
		fn run(self, scheduling: Scheduling) -> (Weight, Option<Self>);
	}

	pub trait RegisterTask<Task> {
		fn register_task(task: Task);
	}

	#[derive(Encode, Decode)]
	struct LazilyRemovePrefix {
		prefix: Vec<u8>,
	}

	impl Task for LazilyRemovePrefix {
		fn run(self, remaining_weight: Weight) -> (Weight, Option<Self>) {
			todo!()
		}
	}

	// Anything that is a runtime upgrade is also a monolithic task.
	impl<T: OnRuntimeUpgrade> Task for T {
		fn run(self, scheduling: Scheduling) -> (Weight, Option<Self>) {
			match scheduling {
				Scheduling::Dispatch => (T::on_runtime_upgrade(), None),
				_ => {
					// This type of task cannot be scheduled on other ways because its weight cannot
					// be known in advance. Do nothing, and kill the task.
					(Zero::zero(), None)
				},
			}
		}
	}

	/// Anything that is a call is also a monotone task.
	#[derive(Encode, Decode)]
	struct DispatchableTask<Call, Origin> {
		call: Call,
		origin: Origin,
	}

	impl<Call: GetDispatchInfo + Dispatchable + Encode + Decode, Origin: Encode + Decode> Task
		for DispatchableTask<Call, Origin>
	{
		fn run(self, scheduling: Scheduling) -> (Weight, Option<Self>) {
			let DispatchableTask { call, origin } = self;
			let weight = self.call.get_dispatch_info();

			if scheduling.can_run(weight) {
				let result = call.dispatch(origin);
				(weight, None)
			} else {
				// we couldn't execute, but we might in the future, so let's retry.
				(Zero::zero(), Some(self))
			}
		}
	}

	#[pallet::pallet]
	pub struct Pallet<T>(_);

	/// Configure the pallet by specifying the parameters and types on which it depends.
	#[pallet::config]
	pub trait Config: frame_system::Config {
		/// Type of the tasks.
		///
		/// This type should always remain backwards compatible; use an enum.
		type Task: Task;
	}

	trait Queue<T> {
		fn queue_pop() -> Option<T>;
		fn queue_get(i: usize) -> Option<T>;
		fn queue_insert(t: T);
	}

	// -------------------------------- SHOULD CHANGE --------------------------------
	#[pallet::storage]
	pub type OffchainWorkerAgenda<T: Config> = StorageValue<_, Vec<T::Task>, ValueQuery>;

	#[pallet::storage]
	pub type OnIdleAgenda<T: Config> = StorageValue<_, Vec<T::Task>, ValueQuery>;

	#[pallet::storage]
	pub type OnInitializeAgenda<T: Config> = StorageValue<_, Vec<T::Task>, ValueQuery>;

	#[pallet::storage]
	pub type DispatchAgenda<T: Config> = StorageValue<_, Vec<T::Task>, ValueQuery>;
	// -------------------------------- SHOULD CHANGE --------------------------------

	impl<T: Config> Queue<T::Task> for OffchainWorkerAgenda<T> {
		fn queue_insert(t: T::Task) {
			OffchainWorkerAgenda::<T>::mutate(|v| v.push(t))
		}

		fn queue_pop() -> Option<T::Task> {
			OffchainWorkerAgenda::<T>::try_mutate(
				|v| if v.is_empty() { Err(()) } else { v.remove(0) },
			)
		}

		fn queue_get(i: usize) -> Option<T::Task> {
			OffchainWorkerAgenda::<T>::get().get(i)
		}
	}

	#[pallet::call]
	impl<T: Config> Pallet<T> {
		#[pallet::weight(provided_weight)]
		pub fn execute_task(origin: OriginFor<T>, provided_weight: Weight) -> DispatchResult {
			let task: T::Task = DispatchAgenda::<T>::queue_pop().unwrap();
			let scheduling = Scheduling::Dispatch;

			let (actual_weight, maybe_leftover) = task.run(scheduling);
			assert_eq!(actual_weight, provided_weight);

			Ok(())
		}

		pub fn register_task(origin: OriginFor<T>, task: T::Task) -> DispatchResult {
			ensure_root(origin);
			todo!();
		}
	}

	#[pallet::hooks]
	impl<T: Config> Hooks<T::BlockNumber> for Pallet<T> {
		fn offchain_worker(_n: T::BlockNumber) {
			// here we have the freedom to do whatever, so let's submit our entire agenda. Then we
			// record in our offchain storage that we have submitted these and are waiting for them
			// to be serviced.

			let mut agenda = Vec::<T::Task>::new();
			while let Some(next) = DispatchAgenda::<T>::queue_pop() {
				agenda.push(next);
			}

			let calls = agenda
				.into_iter()
				.map(|t| {
					// dry-run the task to see how much weight it would consume, in the current
					// state.
					let (weight, _) = t.clone().run(Scheduling::Dispatch);
					let call = Call::execute_task(weight);
					call
				})
				.collect::<Vec<_>>();
		}

		fn on_idle(_: T::BlockNumber, mut remaining_weight: Weight) -> Weight {
			// service exactly one message per round, for now. This is super dead simple, but good
			// enough to start with.
			if let Some(task) = OnIdleAgenda::<T>::queue_pop() {
				let (used_weight, next_task) = task.run(remaining_weight);
				remaining_weight -= used_weight;
				if let Some(next) = next_task {
					OnIdleAgenda::<T>::queue_insert(next);
				}
			}

			remaining_weight
		}
	}
}
