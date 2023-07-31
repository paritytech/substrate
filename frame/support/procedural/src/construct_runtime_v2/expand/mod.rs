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

use crate::construct_runtime_v2::Def;
use crate::construct_runtime_v2::parse::pallets::AllPalletsDeclaration;

pub fn expand(mut def: Def) -> proc_macro2::TokenStream {
    let runtime_struct = runtime_struct::expand_runtime_struct(&mut def);

    match def.pallets {
        (AllPalletsDeclaration::Implicit(decl), result) => {
            println!("Implicit {}", result.clone());
            result
        }
        (AllPalletsDeclaration::Explicit(decl), result) => {
            println!("Explicit");
            result
        }
        (AllPalletsDeclaration::ExplicitExpanded(decl), _) => {
            quote::quote!(
                #runtime_struct
            )
        }
    }
}
