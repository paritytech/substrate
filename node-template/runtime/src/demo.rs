/// module for demonstration purposes and with necessary imports

/// in order to create your runtime module, you need `decl_module` macro imported
/// import `decl_storage` to declare and initialize storage for your module
/// both `decl_module` and `decl_storage` are imported in line 7 below

/// additionally import `decl_event` to declare events for your module

/// feel free to remove or edit this file, as needed
/// in case you remove this file, also make sure to remove line numbers 42, 178, 194 from `../runtime/src/lib.rs`

use support::{decl_module, decl_storage, StorageValue, dispatch::Result};

pub trait Trait: system::Trait {}

decl_module! {
  pub struct Module<T: Trait> for enum Call where origin: T::Origin {
    // simple function that takes a value and stores it
    fn set_value(_origin, value: u32) -> Result {
      <Value<T>>::put(value);
      Ok(())
    }
  }
}

decl_storage! {
  trait Store for Module<T: Trait> as Demo {
    // storage value for an unsigned 32 bit integer
    Value: u32;
  }
}