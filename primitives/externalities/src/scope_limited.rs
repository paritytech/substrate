// This file is part of Substrate.

// Copyright (C) 2019-2021 Parity Technologies (UK) Ltd.
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

//! Stores the externalities in an `environmental` value to make it scope limited available.

use crate::Externalities;

environmental::environmental!(ext: trait Externalities);

/// Set the given externalities while executing the given closure. To get access to the
/// externalities while executing the given closure [`with_externalities`] grants access to them.
/// The externalities are only set for the same thread this function was called from.
pub fn set_and_run_with_externalities<F, R>(ext: &mut dyn Externalities, f: F) -> R
where
	F: FnOnce() -> R,
{
	ext::using(ext, f)
}

/// Execute the given closure with the currently set externalities.
///
/// Returns `None` if no externalities are set or `Some(_)` with the result of the closure.
pub fn with_externalities<F: FnOnce(&mut dyn Externalities) -> R, R>(f: F) -> Option<R> {
	ext::with(f)
}
