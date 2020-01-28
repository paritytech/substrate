use super::*;

use sp_runtime::traits::SaturatedConversion;

use frame_system::RawOrigin;
use sp_io::hashing::blake2_256;

pub fn account<T: Trait>(index: u32) -> T::AccountId {
	let entropy = (b"benchmark", index).using_encoded(blake2_256);
	T::AccountId::decode(&mut &entropy[..]).unwrap_or_default()
}

pub mod set_identity {
	use super::*;

	pub fn components() -> Vec<(BenchmarkParameter, u32, u32)> {
		vec![
			// Registrar Count
			(BenchmarkParameter::R, 1, 16),
			// Additional Field Count
			(BenchmarkParameter::X, 1, 20)
		]
	}

	/// Assumes externalities are set up with a mutable state.
	///
	/// Panics if `component_name` isn't from `set_identity::components` or `component_value` is out of
	/// the range of `set_identity::components`.
	///
	/// Sets up state randomly and returns a randomly generated `set_identity` with sensible (fixed)
	/// values for all complexity components except those mentioned in the identity.
	pub fn instance<T: Trait>(components: &[(BenchmarkParameter, u32)]) -> crate::Call<T>
	{

		// Add r registrars
		let r = components.iter().find(|&c| c.0 == BenchmarkParameter::R).unwrap();
		let _ = T::Currency::deposit_creating(&account::<T>(1), 1_000_000_000_000u128.saturated_into());
		for i in 0..r.1 {
			let _ = T::Currency::deposit_creating(&account::<T>(i), 1_000_000_000_000u128.saturated_into());
			//assert_eq!(crate::Module::<T>::add_registrar(RawOrigin::Signed(account::<T>(1)).into(), account::<T>(i)), Ok(()));
//			assert_eq!(Identity::set_fee(Origin::signed(i.into()), i, 10), Ok(()));
//			let fields = IdentityFields(IdentityField::Display | IdentityField::Legal);
//			assert_eq!(Identity::set_fields(Origin::signed(i.into()), 0, fields), Ok(()));
		}
		
		// Create identity info with x additional fields
		let x = components.iter().find(|&c| c.0 == BenchmarkParameter::X).unwrap();
		// 32 byte data that we reuse below
		let data = Data::Raw(vec![0; 32]);
		let info = IdentityInfo {
			additional: vec![(data.clone(), data.clone()); x.1 as usize],
			display: data.clone(),
			legal: data.clone(),
			web: data.clone(),
			riot: data.clone(),
			email: data.clone(),
			pgp_fingerprint: Some([0; 20]),
			image: data.clone(),
			twitter: data.clone(),
		};

		// Return the `set_identity` call
		crate::Call::<T>::set_identity(info)
	}
}