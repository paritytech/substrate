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

/// The ident used for the block generic parameter.
pub const BLOCK_GENERIC_IDENT: &str = "Block";

/// The `core_trait` attribute.
pub const CORE_TRAIT_ATTRIBUTE: &str = "core_trait";
/// The `api_version` attribute.
///
/// Is used to set the current version of the trait.
pub const API_VERSION_ATTRIBUTE: &str = "api_version";
/// The `changed_in` attribute.
///
/// Is used when the function signature changed between different versions of a trait.
/// This attribute should be placed on the old signature of the function.
pub const CHANGED_IN_ATTRIBUTE: &str = "changed_in";
/// The `renamed` attribute.
///
/// Is used when a trait method was renamed.
pub const RENAMED_ATTRIBUTE: &str = "renamed";
/// All attributes that we support in the declaration of a runtime api trait.
pub const SUPPORTED_ATTRIBUTE_NAMES: &[&str] =
	&[CORE_TRAIT_ATTRIBUTE, API_VERSION_ATTRIBUTE, CHANGED_IN_ATTRIBUTE, RENAMED_ATTRIBUTE];
