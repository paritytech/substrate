// This file is part of Substrate.

// Copyright (C) 2021 Parity Technologies (UK) Ltd.
// SPDX-License-Identifier: GPL-3.0-or-later WITH Classpath-exception-2.0

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with this program. If not, see <https://www.gnu.org/licenses/>.

/// Use this to override host functions.
/// eg
/// ```rust
/// use test_runner::override_host_functions;
/// pub struct SignatureVerificationOverride;
///
/// impl sp_wasm_interface::HostFunctions for SignatureVerificationOverride {
///     fn host_functions() -> Vec<&'static dyn sp_wasm_interface::Function> {
///         override_host_functions!(
///             "ext_crypto_ecdsa_verify_version_1", EcdsaVerify,
///         )
///     }
/// }
/// ```
#[macro_export]
macro_rules! override_host_functions {
    ($($fn_name:expr, $name:ident,)*) => {{
        let mut host_functions = vec![];
        $(
            struct $name;
            impl sp_wasm_interface::Function for $name {
                fn name(&self) -> &str {
                    &$fn_name
                }

                fn signature(&self) -> sp_wasm_interface::Signature {
                    sp_wasm_interface::Signature {
                        args: std::borrow::Cow::Owned(vec![
                            sp_wasm_interface::ValueType::I32,
                            sp_wasm_interface::ValueType::I64,
                            sp_wasm_interface::ValueType::I32,
                        ]),
                        return_value: Some(sp_wasm_interface::ValueType::I32),
                    }
                }

                fn execute(
                    &self,
                    context: &mut dyn sp_wasm_interface::FunctionContext,
                    _args: &mut dyn Iterator<Item = sp_wasm_interface::Value>,
                ) -> Result<Option<sp_wasm_interface::Value>, String> {
                    <bool as sp_runtime_interface::host::IntoFFIValue>::into_ffi_value(true, context)
                        .map(sp_wasm_interface::IntoValue::into_value)
                        .map(Some)
                }
            }
            host_functions.push(&$name as &'static dyn sp_wasm_interface::Function);
        )*
        host_functions
   }};
}

/// Provides host functions that overrides runtime signature verification
/// to always return true.
pub struct SignatureVerificationOverride;

impl sp_wasm_interface::HostFunctions for SignatureVerificationOverride {
    fn host_functions() -> Vec<&'static dyn sp_wasm_interface::Function> {
        override_host_functions!(
            "ext_crypto_ecdsa_verify_version_1", EcdsaVerify,
            "ext_crypto_ed25519_verify_version_1", Ed25519Verify,
            "ext_crypto_sr25519_verify_version_1", Sr25519Verify,
            "ext_crypto_sr25519_verify_version_2", Sr25519VerifyV2,
        )
    }
}
