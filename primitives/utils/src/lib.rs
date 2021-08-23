// This file is part of Substrate.

// Copyright (C) 2020-2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: Apache-2.0

// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
// 	http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! Utilities Primitives for Substrate
//!
//! # Features
//!
//! ## metered
//!
//! This feature changes the behaviour of the function `mpsc::tracing_unbounded`.
//! With the disabled feature this function is an alias to `futures::channel::mpsc::unbounded`.
//! However, when the feature is enabled it creates wrapper types to `UnboundedSender<T>`
//! and `UnboundedReceiver<T>` to register every `send`/`received`/`dropped` action happened on
//! the channel.
//!
//! Also this feature creates and registers a prometheus vector with name `unbounded_channel_len`
//! and labels:
//!
//! | Label        | Description                                   |
//! | ------------ | --------------------------------------------- |
//! | entity       | Name of channel passed to `tracing_unbounded` |
//! | action       | One of `send`/`received`/`dropped`            |

pub mod metrics;
pub mod mpsc;
pub mod status_sinks;
