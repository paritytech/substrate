macro_rules! reserved {
	($($reserved:ident)*) => {
		$(
			mod $reserved {
				pub use support::dispatch::Result;

				pub trait Trait {
					type Origin;
					type BlockNumber: Into<u32>;
				}

				pub mod system {
					use support::dispatch::Result;

					pub fn ensure_root<R>(_: R) -> Result {
						Ok(())
					}
				}

				support::decl_module! {
					pub struct Module<T: Trait> for enum Call where origin: T::Origin {
						fn $reserved(_origin) -> Result { unreachable!() }
					}
				}
			}
		)*
	}
}

reserved!(on_finalize on_initialize on_finalise on_initialise offchain_worker deposit_event);

fn main() {}
