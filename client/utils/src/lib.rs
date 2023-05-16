// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

//! Utilities Primitives for Substrate
//!
//! This crate provides `mpsc::tracing_unbounded` function that returns wrapper types to
//! `async_channel::Sender<T>` and `async_channel::Receiver<T>`, which register every
//! `send`/`received`/`dropped` action happened on the channel.
//!
//! Also this wrapper creates and registers a prometheus vector with name `unbounded_channel_len`
//! and labels:
//!
//! | Label        | Description                                   |
//! | ------------ | --------------------------------------------- |
//! | entity       | Name of channel passed to `tracing_unbounded` |
//! | action       | One of `send`/`received`/`dropped`            |

pub mod id_sequence;
pub mod metrics;
pub mod mpsc;
pub mod notification;
pub mod pubsub;
pub mod status_sinks;
