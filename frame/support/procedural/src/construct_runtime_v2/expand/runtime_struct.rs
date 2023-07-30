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

use crate::construct_runtime_v2::expand::Def;

pub fn expand_runtime_struct(def: &mut Def) -> proc_macro2::TokenStream {
    let runtime_ident = &def.runtime_struct.ident;

    quote::quote_spanned!(def.runtime_struct.attr_span =>
        pub struct #runtime_ident;
    )
}
