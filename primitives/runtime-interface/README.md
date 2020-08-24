Substrate runtime interface

This crate provides types, traits and macros around runtime interfaces. A runtime interface is
a fixed interface between a Substrate runtime and a Substrate node. For a native runtime the
interface maps to a direct function call of the implementation. For a wasm runtime the interface
maps to an external function call. These external functions are exported by the wasm executor
and they map to the same implementation as the native calls.

# Using a type in a runtime interface

Any type that should be used in a runtime interface as argument or return value needs to
implement [`RIType`]. The associated type [`FFIType`](RIType::FFIType) is the type that is used
in the FFI function to represent the actual type. For example `[T]` is represented by an `u64`.
The slice pointer and the length will be mapped to an `u64` value. For more information see
this [table](#ffi-type-and-conversion). The FFI function definition is used when calling from
the wasm runtime into the node.

Traits are used to convert from a type to the corresponding [`RIType::FFIType`].
Depending on where and how a type should be used in a function signature, a combination of the
following traits need to be implemented:

1. Pass as function argument: [`wasm::IntoFFIValue`] and [`host::FromFFIValue`]
2. As function return value: [`wasm::FromFFIValue`] and [`host::IntoFFIValue`]
3. Pass as mutable function argument: [`host::IntoPreallocatedFFIValue`]

The traits are implemented for most of the common types like `[T]`, `Vec<T>`, arrays and
primitive types.

For custom types, we provide the [`PassBy`](pass_by::PassBy) trait and strategies that define
how a type is passed between the wasm runtime and the node. Each strategy also provides a derive
macro to simplify the implementation.

# Performance

To not waste any more performance when calling into the node, not all types are SCALE encoded
when being passed as arguments between the wasm runtime and the node. For most types that
are raw bytes like `Vec<u8>`, `[u8]` or `[u8; N]` we pass them directly, without SCALE encoding
them in front of. The implementation of [`RIType`] each type provides more information on how
the data is passed.

# Declaring a runtime interface

Declaring a runtime interface is similar to declaring a trait in Rust:

```rust
#[sp_runtime_interface::runtime_interface]
trait RuntimeInterface {
    fn some_function(value: &[u8]) -> bool {
        value.iter().all(|v| *v > 125)
    }
}
```

For more information on declaring a runtime interface, see
[`#[runtime_interface]`](attr.runtime_interface.html).

# FFI type and conversion

The following table documents how values of types are passed between the wasm and
the host side and how they are converted into the corresponding type.

| Type | FFI type | Conversion |
|----|----|----|
| `u8` | `u8` | `Identity` |
| `u16` | `u16` | `Identity` |
| `u32` | `u32` | `Identity` |
| `u64` | `u64` | `Identity` |
| `i128` | `u32` | `v.as_ptr()` (pointer to a 16 byte array) |
| `i8` | `i8` | `Identity` |
| `i16` | `i16` | `Identity` |
| `i32` | `i32` | `Identity` |
| `i64` | `i64` | `Identity` |
| `u128` | `u32` | `v.as_ptr()` (pointer to a 16 byte array) |
| `bool` | `u8` | `if v { 1 } else { 0 }` |
| `&str` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
| `&[u8]` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
| `Vec<u8>` | `u64` | <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |
| `Vec<T> where T: Encode` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
| `&[T] where T: Encode` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
| `[u8; N]` | `u32` | `v.as_ptr()` |
| `*const T` | `u32` | `Identity` |
| `Option<T>` | `u64` | `let e = v.encode();`<br><br><code>e.len() 32bit << 32 &#124; e.as_ptr() 32bit</code> |
| [`T where T: PassBy<PassBy=Inner>`](pass_by::Inner) | Depends on inner | Depends on inner |
| [`T where T: PassBy<PassBy=Codec>`](pass_by::Codec) | `u64`| <code>v.len() 32bit << 32 &#124; v.as_ptr() 32bit</code> |

`Identity` means that the value is converted directly into the corresponding FFI type.

License: Apache-2.0