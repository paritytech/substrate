// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

//! Async externalities.

use sp_std::{
	boxed::Box,
	any::{TypeId, Any},
	vec::Vec,
};
use sp_core::{
	storage::{ChildInfo, TrackedStorageKey},
	traits::{SpawnNamed, TaskExecutorExt, RuntimeSpawnExt, RuntimeSpawn},
};
use sp_externalities::{
	Externalities, Extensions, ExternalitiesExt as _, TaskId, WorkerResult,
	AsyncExternalities as AsyncExternalitiesTrait,
	ambassador_impl_Externalities_body_single_struct,
};

// Module to expose AsyncExternalities without alias to delegate macro.
mod async_ext_def {
	use ambassador::Delegate;
	use super::*;
	use sp_externalities::AsyncExternalities;

	/// Simple state-less externalities for use in async context.
	///
	/// Will panic if anything is accessing the storage.
	#[derive(Delegate)]
	#[delegate(Externalities, target = "state")]
	pub struct AsyncExternalitiesImpl {
		pub(super) extensions: Extensions,
		pub(super) state: Box<dyn AsyncExternalities>,
	}
}

pub use async_ext_def::AsyncExternalitiesImpl as AsyncExternalities;

/// New Async externalities.
#[cfg(feature = "std")]
pub fn new_async_externalities(
	scheduler: Box<dyn SpawnNamed>,
	async_ext: Box<dyn AsyncExternalitiesTrait>,
) -> Result<AsyncExternalities, &'static str> {
	let mut res = AsyncExternalities {
		extensions: Default::default(),
		state: async_ext,
	};
	let mut ext = &mut res as &mut dyn Externalities;
	ext.register_extension::<TaskExecutorExt>(TaskExecutorExt(scheduler.clone()))
		.map_err(|_| "Failed to register task executor extension.")?;

	Ok(res)
}

/// New Async externalities.
/// This variant do not add task executor extension
/// and can run inline only.
pub fn new_inline_only_externalities(
	async_ext: Box<dyn AsyncExternalitiesTrait>,
) -> Result<AsyncExternalities, &'static str> {
	Ok(AsyncExternalities {
		extensions: Default::default(),
		state: async_ext,
	})
}

impl AsyncExternalities {
	/// Extend async externalities with the ability to spawn wasm instances.
	pub fn with_runtime_spawn(
		mut self,
		runtime_ext: Box<dyn RuntimeSpawn>,
	) -> Result<Self, &'static str> {
		let mut ext = &mut self as &mut dyn Externalities;
		ext.register_extension::<RuntimeSpawnExt>(RuntimeSpawnExt(runtime_ext))
			.map_err(|_| "Failed to register task executor extension.")?;

		Ok(self)
	}
}

impl sp_externalities::ExtensionStore for AsyncExternalities {
	fn extension_by_type_id(&mut self, type_id: TypeId) -> Option<&mut dyn Any> {
		self.extensions.get_mut(type_id)
	}

	fn register_extension_with_type_id(
		&mut self,
		type_id: TypeId,
		extension: Box<dyn sp_externalities::Extension>,
	) -> Result<(), sp_externalities::Error> {
		self.extensions.register_with_type_id(type_id, extension)
	}

	fn deregister_extension_by_type_id(&mut self, type_id: TypeId) -> Result<(), sp_externalities::Error> {
		if self.extensions.deregister(type_id) {
			Ok(())
		} else {
			Err(sp_externalities::Error::ExtensionIsNotRegistered(type_id))
		}
	}
}

impl AsyncExternalitiesTrait for AsyncExternalities { }
