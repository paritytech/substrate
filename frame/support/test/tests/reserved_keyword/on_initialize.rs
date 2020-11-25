macro_rules! reserved {
	($($reserved:ident)*) => {
		$(
			mod $reserved {
				pub use frame_support::dispatch;

				pub trait Config: frame_support_test::Config {}

				pub mod system {
					use frame_support::dispatch;

					pub fn ensure_root<R>(_: R) -> dispatch::DispatchResult {
						Ok(())
					}
				}

				frame_support::decl_module! {
					pub struct Module<T: Config> for enum Call where origin: T::Origin, system=frame_support_test {
						#[weight = 0]
						fn $reserved(_origin) -> dispatch::DispatchResult { unreachable!() }
					}
				}
			}
		)*
	}
}

reserved!(on_finalize on_initialize on_runtime_upgrade offchain_worker deposit_event);

fn main() {}
