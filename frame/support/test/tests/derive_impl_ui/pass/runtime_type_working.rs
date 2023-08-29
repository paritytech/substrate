use frame_support::{*, pallet_prelude::inject_runtime_type};
use static_assertions::assert_type_eq_all;

pub trait Config {
    type RuntimeCall;
}

type RuntimeCall = u32;

struct Pallet;

#[register_default_impl(Pallet)]
impl Config for Pallet {
    #[inject_runtime_type]
    type RuntimeCall = ();
}

struct SomePallet;

#[derive_impl(Pallet)] // Injects type RuntimeCall = RuntimeCall;
impl Config for SomePallet {}

assert_type_eq_all!(<SomePallet as Config>::RuntimeCall, u32);

fn main() {}
