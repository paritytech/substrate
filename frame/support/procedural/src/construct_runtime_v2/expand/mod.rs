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

mod runtime_struct;
mod event;

use crate::construct_runtime_v2::parse::Def;
use frame_support_procedural_tools::{
	generate_crate_access, generate_crate_access_2018, generate_hidden_includes,
};

pub fn expand(mut def: Def) -> proc_macro2::TokenStream {
    let name = &def.runtime_struct.ident.clone();

    let hidden_crate_name = "construct_runtime_v2";
    let scrate = generate_crate_access(hidden_crate_name, "frame-support");
    let scrate_decl = generate_hidden_includes(hidden_crate_name, "frame-support");

    let runtime_struct = runtime_struct::expand_runtime_struct(&mut def);

    let outer_event = event::expand_outer_event(&name, &def.pallets.pallets, &scrate).unwrap(); //Todo

    quote::quote!(
      #runtime_struct

      #outer_event
    )
}