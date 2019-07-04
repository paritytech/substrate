macro_rules! reserved {
	($($reserved:ident)*) => {
		$(
			mod $reserved {
				pub use srml_support::dispatch::Result;

				pub trait Trait {
					type Origin;
					type BlockNumber: Into<u32>;
				}

				pub mod system {
					use srml_support::dispatch::Result;

					pub fn ensure_root<R>(_: R) -> Result {
						Ok(())
					}
				}

				srml_support::decl_module! {
					pub struct Module<T: Trait> for enum Call where origin: T::Origin {
						fn $reserved() -> Result { unreachable!() }
					}
				}
			}
		)*
	}
}

reserved!(on_finalize on_initialize on_finalise on_initialise offchain_worker deposit_event);

fn main() {
}
