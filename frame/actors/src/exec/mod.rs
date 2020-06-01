mod runtime;

pub use self::runtime::Ext;

use sp_std::collections::btree_map::BTreeMap;
use frame_support::{traits::{Get, ReservableCurrency}, storage::StorageMap};
use self::runtime::env_def::FunctionImplProvider;
use crate::{AccountIdFor, MessageFor, BalanceFor, ActorInfoOf, StorageKey, Message, Trait};

pub struct MemorySchedule {
	pub initial: u32,
	pub maximum: Option<u32>,
}

pub fn execute<E: Ext>(
	code: &[u8],
	entrypoint_name: &'static str,
	ext: &mut E,
	input_data: Vec<u8>,
	memory_schedule: &MemorySchedule,
) -> Result<(), ()> {
	let memory = sp_sandbox::Memory::new(memory_schedule.initial, memory_schedule.maximum)
		.unwrap_or_else(|_| {
			// unlike `.expect`, explicit panic preserves the source location.
			// Needed as we can't use `RUST_BACKTRACE` in here.
			panic!(
				"exec.prefab_module.initial can't be greater than exec.prefab_module.maximum;
						thus Memory::new must not fail;
						qed"
			)
		});

	let mut imports = sp_sandbox::EnvironmentDefinitionBuilder::new();
	imports.add_memory("env", "memory", memory.clone());
	runtime::Env::impls(&mut |name, func_ptr| {
		imports.add_host_func("env", name, func_ptr);
	});

	let mut runtime = runtime::Runtime::new(
		ext,
		input_data,
		memory,
	);

	sp_sandbox::Instance::new(code, &imports, &mut runtime)
		.and_then(|mut instance| instance.invoke(entrypoint_name, &[], &mut runtime))
		.map(|_| ())
		.map_err(|_| ())
}

pub struct Context<T: Trait> {
	account_id: AccountIdFor<T>,
	storage_changes: BTreeMap<StorageKey, Option<Vec<u8>>>,
	message: MessageFor<T>,
	outgoing_messages: Vec<(AccountIdFor<T>, MessageFor<T>)>,
}

impl<T: Trait> Context<T> {
	pub fn new(account_id: AccountIdFor<T>, message: MessageFor<T>) -> Self {
		Self {
			account_id,
			storage_changes: BTreeMap::new(),
			outgoing_messages: Vec::new(),
			message,
		}
	}

	pub fn apply(self) {
		let storage_changes = self.storage_changes;
		ActorInfoOf::<T>::mutate(self.account_id.clone(), |actor| {
			for (key, value) in storage_changes {
				match value {
					Some(value) => {
						actor.storage.insert(key, value);
					},
					None => {
						actor.storage.remove(&key);
					},
				}
			}
		});

		for (target, message) in self.outgoing_messages {
			ActorInfoOf::<T>::mutate(target, |actor| {
				actor.messages.push(message);
			});
		}
	}
}

impl<T: Trait> Ext for Context<T> {
	type T = T;

	fn get_storage(&self, key: &StorageKey) -> Option<Vec<u8>> {
		if let Some(value) = self.storage_changes.get(key) {
			return value.clone()
		}

		ActorInfoOf::<T>::get(self.account_id.clone()).storage.get(key).cloned()
	}

	fn set_storage(&mut self, key: StorageKey, value: Option<Vec<u8>>) -> Result<(), &'static str> {
		if let Some(value) = &value {
			if value.len() > self.max_value_size() as usize {
				return Err("Storage exceeded maximum value size")
			}
		}

		self.storage_changes.insert(key, value);
		Ok(())
	}

	fn send_message(
		&mut self,
		target: AccountIdFor<Self::T>,
		value: BalanceFor<Self::T>,
		data: Vec<u8>,
	) -> Result<(), &'static str> {
		if data.len() > self.max_value_size() as usize {
			return Err("Message data exceeded maximum value size")
		}

		T::Currency::reserve(&self.account_id, value).map(|_| "Reserve fund failed")?;

		let message = Message {
			source: self.account_id.clone(),
			value,
			data,
		};

		self.outgoing_messages.push((target, message));
		Ok(())
	}

	fn get_message(&self) -> MessageFor<Self::T> {
		self.message.clone()
	}

	fn max_value_size(&self) -> u32 {
		T::MaxValueSize::get()
	}
}
