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

//! Implementation of the trait instance and the instance structures implementing it.
//! (For not instantiable traits there is still the inherent instance implemented).

use super::DeclStorageDefExt;
use crate::NUMBER_OF_INSTANCE;
use proc_macro2::{Span, TokenStream};
use quote::quote;

pub(crate) const INHERENT_INSTANCE_NAME: &str = "__InherentHiddenInstance";
