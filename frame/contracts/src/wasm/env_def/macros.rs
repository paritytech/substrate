// This file is part of Substrate.

// Copyright (C) 2018-2022 Parity Technologies (UK) Ltd.
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

/// Since we can't specify the type of closure directly at binding site:
///
/// ```nocompile
/// let f: FnOnce() -> Result<<u32 as ConvertibleToWasm>::NativeType, _> = || { /* ... */ };
/// ```
///
/// we use this function to constrain the type of the closure.
#[inline(always)]
pub fn constrain_closure<R, F>(f: F) -> F
where
	F: FnOnce() -> Result<R, crate::wasm::runtime::TrapReason>,
{
	f
}
