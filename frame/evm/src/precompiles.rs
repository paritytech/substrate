use sp_std::vec::Vec;
use sp_core::H160;
use evm::{ExitError, ExitSucceed};

/// Custom precompiles to be used by EVM engine.
pub trait Precompiles {
	/// Try to execute the code address as precompile. If the code address is not
	/// a precompile or the precompile is not yet available, return `None`.
	/// Otherwise, calculate the amount of gas needed with given `input` and
	/// `target_gas`. Return `Some(Ok(status, output, gas_used))` if the execution
	/// is successful. Otherwise return `Some(Err(_))`.
	fn execute(
		address: H160,
		input: &[u8],
		target_gas: Option<usize>,
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>>;
}

impl Precompiles for () {
	fn execute(
		_address: H160,
		_input: &[u8],
		_target_gas: Option<usize>
	) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>> {
		None
	}
}

/// One single precompile used by EVM engine.
pub trait Precompile {
	/// Try to execute the precompile. Calculate the amount of gas needed with given `input` and
	/// `target_gas`. Return `Ok(status, output, gas_used)` if the execution is
	/// successful. Otherwise return `Err(_)`.
	fn execute(
		input: &[u8],
		target_gas: Option<usize>,
	) -> core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>;
}

macro_rules! impl_precompile_tuple {
	( ($($item:ident,)+) ) => {
		impl<$($item: Precompile,)+> Precompiles for ($($item,)+) {
			fn execute(
				address: H160,
				input: &[u8],
				target_gas: Option<usize>,
			) -> Option<core::result::Result<(ExitSucceed, Vec<u8>, usize), ExitError>> {
				let mut index = 0;

				$(
					index += 1;
					if address == H160::from_low_u64_be(index) {
						return Some($item::execute(input, target_gas))
					}
				)+

				None
			}
		}
	};
}

impl_precompile_tuple!((A,));
impl_precompile_tuple!((A,B,));
impl_precompile_tuple!((A,B,C,));
impl_precompile_tuple!((A,B,C,D,));
impl_precompile_tuple!((A,B,C,D,E,));
impl_precompile_tuple!((A,B,C,D,E,F,));
impl_precompile_tuple!((A,B,C,D,E,F,G,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,L,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,L,M,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,L,M,N,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,));
impl_precompile_tuple!((A,B,C,D,E,F,G,H,I,J,K,L,M,N,O,P,));
