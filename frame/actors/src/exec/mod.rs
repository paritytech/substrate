#[macro_use]
mod env_def;
mod runtime;
mod prepare;
mod code_cache;

pub use self::runtime::{Runtime, Ext};
pub use self::code_cache::{load as load_code, save as save_code};

use codec::{Encode, Decode};
use sp_std::collections::btree_map::BTreeMap;
use frame_support::{traits::ReservableCurrency, storage::StorageMap};
use crate::{
	AccountIdFor, MessageFor, BalanceFor, ActorInfoOf, StorageKey, Message, Trait, HashFor,
	Schedule, Gas, gas::GasMeter, Module,
};
use crate::exec::env_def::FunctionImplProvider;

/// A prepared wasm module ready for execution.
#[derive(Clone, Encode, Decode)]
pub struct PrefabWasmModule {
	/// Version of the schedule with which the code was instrumented.
	#[codec(compact)]
	schedule_version: u32,
	#[codec(compact)]
	initial: u32,
	#[codec(compact)]
	maximum: u32,
	/// This field is reserved for future evolution of format.
	///
	/// Basically, for now this field will be serialized as `None`. In the future
	/// we would be able to extend this structure with.
	_reserved: Option<()>,
	/// Code instrumented with the latest schedule.
	code: Vec<u8>,
}

pub fn execute<T: Trait, E: Ext<T=T>>(
	module: &PrefabWasmModule,
	entrypoint_name: &'static str,
	input_data: Vec<u8>,
	ext: &mut E,
	schedule: &Schedule,
	gas_limit: Gas,
) -> Result<(), ()> {
	let memory = sp_sandbox::Memory::new(module.initial, Some(module.maximum))
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

	let mut gas_meter = GasMeter::<T>::new(gas_limit);
	let mut runtime = runtime::Runtime::new(
		ext,
		input_data,
		schedule,
		memory,
		&mut gas_meter,
	);

	sp_sandbox::Instance::new(&module.code, &imports, &mut runtime)
		.and_then(|mut instance| instance.invoke(entrypoint_name, &[], &mut runtime))
		.map(|_| ())
		.map_err(|_| ())
}

pub struct Context<'a, T: Trait> {
	account_id: AccountIdFor<T>,
	storage_changes: BTreeMap<StorageKey, Option<Vec<u8>>>,
	message: MessageFor<T>,
	outgoing_messages: Vec<(AccountIdFor<T>, MessageFor<T>)>,
	schedule: &'a Schedule,
}

impl<'a, T: Trait> Context<'a, T> {
	pub fn new(schedule: &'a Schedule, account_id: AccountIdFor<T>, message: MessageFor<T>) -> Self {
		Self {
			schedule,
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
			Module::<T>::store_message(target, message);
		}
	}
}

impl<'a, T: Trait> Ext for Context<'a, T> {
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
		topics: Vec<HashFor<Self::T>>,
		data: Vec<u8>,
	) -> Result<(), &'static str> {
		if data.len() > self.max_value_size() as usize {
			return Err("Message data exceeded maximum value size")
		}

		T::Currency::reserve(&self.account_id, value).map(|_| "Reserve fund failed")?;

		let message = Message {
			source: self.account_id.clone(),
			value,
			topics,
			data,
		};

		self.outgoing_messages.push((target, message));
		Ok(())
	}

	fn get_message(&self) -> MessageFor<Self::T> {
		self.message.clone()
	}

	fn max_value_size(&self) -> u32 {
		self.schedule.max_value_size
	}
}
