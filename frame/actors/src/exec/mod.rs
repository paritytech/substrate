mod runtime;

pub use self::runtime::Ext;

use sp_std::collections::btree_map::BTreeMap;
use frame_support::{traits::Get, storage::StorageMap};
use self::runtime::env_def::FunctionImplProvider;
use crate::{AccountIdFor, MessageFor, ActorInfoOf, StorageKey, Trait};

pub struct MemorySchedule {
	pub initial: u32,
	pub maximum: Option<u32>,
}

pub fn execute<E: Ext>(
	code: &[u8],
	entrypoint_name: &'static str,
	mut ext: E,
	input_data: Vec<u8>,
	memory_schedule: &MemorySchedule,
) {
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
		&mut ext,
		input_data,
		memory,
	);

	sp_sandbox::Instance::new(code, &imports, &mut runtime)
		.and_then(|mut instance| instance.invoke(entrypoint_name, &[], &mut runtime));
}

pub struct Context<T: Trait> {
	account_id: AccountIdFor<T>,
	storage_changes: BTreeMap<StorageKey, Option<Vec<u8>>>,
	message: MessageFor<T>,
	outgoing_messages: Vec<MessageFor<T>>,
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

	fn send_message(&mut self, message: MessageFor<Self::T>) -> Result<(), &'static str> {
		if message.data.len() > self.max_value_size() as usize {
			return Err("Message data exceeded maximum value size")
		}

		self.outgoing_messages.push(message);
		Ok(())
	}

	fn get_message(&self) -> MessageFor<Self::T> {
		self.message.clone()
	}

	fn max_value_size(&self) -> u32 {
		T::MaxValueSize::get()
	}
}
