// This file is part of Substrate.

// Copyright (C) Parity Technologies (UK) Ltd.
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

use crate::interface::parse::Def;
use frame_support_procedural_tools::generate_crate_access_2018;

pub fn expand(mut def: Def) -> proc_macro2::TokenStream {
	let frame_system = generate_crate_access_2018("frame-system")?;
	let frame_support = generate_crate_access_2018("frame-support")?;

	todo!()
}
