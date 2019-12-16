macro_rules! reserved {
	($($reserved:ident)*) => {
		$(
			mod $reserved {
				pub use frame_support::dispatch;

				pub trait Trait {
					type Origin;
					type BlockNumber: Into<u32>;
				}

				pub mod system {
					use frame_support::dispatch;

					pub fn ensure_root<R>(_: R) -> dispatch::Result {
						Ok(())
					}
				}

				frame_support::decl_module! {
					pub struct Module<T: Trait> for enum Call where origin: T::Origin {
						fn $reserved(_origin) -> dispatch::Result { unreachable!() }
					}
				}
			}
		)*
	}
}

reserved!(on_finalize on_initialize on_finalise on_initialise offchain_worker deposit_event);

fn main() {}
