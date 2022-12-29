// This file is part of Substrate.

// Copyright (C) 2019-2022 Parity Technologies (UK) Ltd.
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

pub trait Config: frame_support_test::Config {}

frame_support::decl_module! {
	pub struct Module<T: Config> for enum Call where origin: T::RuntimeOrigin, system=frame_support_test {}
}

frame_support::decl_storage!{
	trait Store for Module<T: Config> as FinalKeysNone {
		pub Value get(fn value) config(): u32;
		pub Value2 config(value): u32;
	}
}

fn main() {}
