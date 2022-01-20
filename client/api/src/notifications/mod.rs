// This file is part of Substrate.

// Copyright (C) 2017-2022 Parity Technologies (UK) Ltd.
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

//! Storage notifications

use std::{
	collections::{HashMap, HashSet},
	sync::Arc,
};

use prometheus_endpoint::Registry as PrometheusRegistry;

use sp_core::storage::{StorageData, StorageKey};

mod keys;
mod registry;
mod storage_change_set;
mod storage_event_stream;
mod storage_notifications;

use keys::{ChildKeys, Keys};
use registry::StorageNotificationsImpl;

/// A type of a message delivered to the subscribers
pub type Notification<Hash> = (Hash, StorageChangeSet);

pub use storage_change_set::StorageChangeSet;
pub use storage_event_stream::StorageEventStream;
pub use storage_notifications::StorageNotifications;

#[cfg(test)]
mod tests;
