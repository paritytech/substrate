#![macro_use]
extern crate ark_relations;

pub mod fields {
	use ark_ff::{BitIteratorLE, Field, PrimeField, UniformRand};
	use ark_r1cs_std::prelude::*;
	use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
	use ark_std::{test_rng, vec::Vec};

	pub fn field_test<F, ConstraintF, AF>() -> Result<(), SynthesisError>
	where
		F: Field,
		ConstraintF: PrimeField,
		AF: FieldVar<F, ConstraintF>,
		AF: TwoBitLookupGadget<ConstraintF, TableConstant = F>,
		for<'a> &'a AF: FieldOpsBounds<'a, F, AF>,
	{
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let cs = ConstraintSystem::<ConstraintF>::new_ref();

			let mut rng = test_rng();
			let a_native = F::rand(&mut rng);
			let b_native = F::rand(&mut rng);
			let a = AF::new_variable(ark_relations::ns!(cs, "generate_a"), || Ok(a_native), mode)?;
			let b = AF::new_variable(ark_relations::ns!(cs, "generate_b"), || Ok(b_native), mode)?;
			let b_const = AF::new_constant(ark_relations::ns!(cs, "b_as_constant"), b_native)?;

			let zero = AF::zero();
			let zero_native = zero.value()?;
			zero.enforce_equal(&zero)?;

			let one = AF::one();
			let one_native = one.value()?;
			one.enforce_equal(&one)?;

			one.enforce_not_equal(&zero)?;

			let one_dup = &zero + &one;
			one_dup.enforce_equal(&one)?;

			let two = &one + &one;
			two.enforce_equal(&two)?;
			two.enforce_equal(&one.double()?)?;
			two.enforce_not_equal(&one)?;
			two.enforce_not_equal(&zero)?;

			// a + 0 = a
			let a_plus_zero = &a + &zero;
			assert_eq!(a_plus_zero.value()?, a_native);
			a_plus_zero.enforce_equal(&a)?;
			a_plus_zero.enforce_not_equal(&a.double()?)?;

			// a - 0 = a
			let a_minus_zero = &a - &zero;
			assert_eq!(a_minus_zero.value()?, a_native);
			a_minus_zero.enforce_equal(&a)?;

			// a - a = 0
			let a_minus_a = &a - &a;
			assert_eq!(a_minus_a.value()?, zero_native);
			a_minus_a.enforce_equal(&zero)?;

			// a + b = b + a
			let a_b = &a + &b;
			let b_a = &b + &a;
			assert_eq!(a_b.value()?, a_native + &b_native);
			a_b.enforce_equal(&b_a)?;

			// (a + b) + a = a + (b + a)
			let ab_a = &a_b + &a;
			let a_ba = &a + &b_a;
			assert_eq!(ab_a.value()?, a_native + &b_native + &a_native);
			ab_a.enforce_equal(&a_ba)?;

			let b_times_a_plus_b = &a_b * &b;
			let b_times_b_plus_a = &b_a * &b;
			assert_eq!(b_times_a_plus_b.value()?, b_native * &(b_native + &a_native));
			assert_eq!(b_times_a_plus_b.value()?, (b_native + &a_native) * &b_native);
			assert_eq!(b_times_a_plus_b.value()?, (a_native + &b_native) * &b_native);
			b_times_b_plus_a.enforce_equal(&b_times_a_plus_b)?;

			// a * 1 = a
			assert_eq!((&a * &one).value()?, a_native * &one_native);

			// a * b = b * a
			let ab = &a * &b;
			let ba = &b * &a;
			assert_eq!(ab.value()?, ba.value()?);
			assert_eq!(ab.value()?, a_native * &b_native);

			let ab_const = &a * &b_const;
			let b_const_a = &b_const * &a;
			assert_eq!(ab_const.value()?, b_const_a.value()?);
			assert_eq!(ab_const.value()?, ab.value()?);
			assert_eq!(ab_const.value()?, a_native * &b_native);

			// (a * b) * a = a * (b * a)
			let ab_a = &ab * &a;
			let a_ba = &a * &ba;
			assert_eq!(ab_a.value()?, a_ba.value()?);
			assert_eq!(ab_a.value()?, a_native * &b_native * &a_native);

			let aa = &a * &a;
			let a_squared = a.square()?;
			a_squared.enforce_equal(&aa)?;
			assert_eq!(aa.value()?, a_squared.value()?);
			assert_eq!(aa.value()?, a_native.square());

			let aa = &a * a_native;
			a_squared.enforce_equal(&aa)?;
			assert_eq!(aa.value()?, a_squared.value()?);
			assert_eq!(aa.value()?, a_native.square());

			let a_b2 = &a + b_native;
			a_b.enforce_equal(&a_b2)?;
			assert_eq!(a_b.value()?, a_b2.value()?);

			let a_inv = a.inverse()?;
			a_inv.mul_equals(&a, &one)?;
			assert_eq!(a_inv.value()?, a.value()?.inverse().unwrap());
			assert_eq!(a_inv.value()?, a_native.inverse().unwrap());

			let a_b_inv = a.mul_by_inverse(&b)?;
			a_b_inv.mul_equals(&b, &a)?;
			assert_eq!(a_b_inv.value()?, a_native * b_native.inverse().unwrap());

			// a * a * a = a^3
			let bits = BitIteratorLE::without_trailing_zeros([3u64])
				.map(Boolean::constant)
				.collect::<Vec<_>>();
			assert_eq!(a_native.pow([0x3]), a.pow_le(&bits)?.value()?);

			// a * a * a = a^3
			assert_eq!(a_native.pow([0x3]), a.pow_by_constant(&[0x3])?.value()?);
			assert!(cs.is_satisfied().unwrap());

			let mut constants = [F::zero(); 4];
			for c in &mut constants {
				*c = UniformRand::rand(&mut test_rng());
			}
			let bits = [Boolean::<ConstraintF>::constant(false), Boolean::constant(true)];
			let lookup_result = AF::two_bit_lookup(&bits, constants.as_ref())?;
			assert_eq!(lookup_result.value()?, constants[2]);
			assert!(cs.is_satisfied().unwrap());

			let f = F::from(1u128 << 64);
			let f_bits = ark_ff::BitIteratorLE::new(&[0u64, 1u64]).collect::<Vec<_>>();
			let fv = AF::new_variable(ark_relations::ns!(cs, "alloc u128"), || Ok(f), mode)?;
			assert_eq!(fv.to_bits_le()?.value().unwrap()[..128], f_bits[..128]);
			assert!(cs.is_satisfied().unwrap());

			let r_native: F = UniformRand::rand(&mut test_rng());

			let r = AF::new_variable(ark_relations::ns!(cs, "r_native"), || Ok(r_native), mode)
				.unwrap();
			let _ = r.to_non_unique_bits_le()?;
			assert!(cs.is_satisfied().unwrap());
			let _ = r.to_bits_le()?;
			assert!(cs.is_satisfied().unwrap());

			let ab_false = &a + (AF::from(Boolean::Constant(false)) * b_native);
			let ab_true = &a + (AF::from(Boolean::Constant(true)) * b_native);
			assert_eq!(ab_false.value()?, a_native);
			assert_eq!(ab_true.value()?, a_native + &b_native);

			if !cs.is_satisfied().unwrap() {
				panic!("Unsatisfied in mode {:?}.\n{:?}", mode, cs.which_is_unsatisfied().unwrap());
			}
			assert!(cs.is_satisfied().unwrap());
		}
		Ok(())
	}

	pub fn frobenius_tests<F: Field, ConstraintF, AF>(maxpower: usize) -> Result<(), SynthesisError>
	where
		F: Field,
		ConstraintF: Field,
		AF: FieldVar<F, ConstraintF>,
		for<'a> &'a AF: FieldOpsBounds<'a, F, AF>,
	{
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let cs = ConstraintSystem::<ConstraintF>::new_ref();
			let mut rng = test_rng();
			for i in 0..=maxpower {
				let mut a = F::rand(&mut rng);
				let mut a_gadget = AF::new_variable(ark_relations::ns!(cs, "a"), || Ok(a), mode)?;
				a_gadget.frobenius_map_in_place(i)?;
				a.frobenius_map(i);

				assert_eq!(a_gadget.value()?, a);
			}

			assert!(cs.is_satisfied().unwrap());
		}
		Ok(())
	}
}

pub mod curves {
	use ark_ec::{
		short_weierstrass::Projective as SWProjective, twisted_edwards::Projective as TEProjective,
		CurveGroup, Group,
	};
	use ark_ff::{BitIteratorLE, Field, One, PrimeField};
	use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
	use ark_std::{test_rng, vec::Vec, UniformRand};

	use ark_r1cs_std::prelude::*;

	pub fn group_test<C, ConstraintF, GG>() -> Result<(), SynthesisError>
	where
		C: CurveGroup,
		ConstraintF: Field,
		GG: CurveVar<C, ConstraintF>,
		for<'a> &'a GG: GroupOpsBounds<'a, C, GG>,
	{
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let cs = ConstraintSystem::<ConstraintF>::new_ref();

			let mut rng = test_rng();
			let a_native = C::rand(&mut rng);
			let b_native = C::rand(&mut rng);
			let a = GG::new_variable(ark_relations::ns!(cs, "generate_a"), || Ok(a_native), mode)
				.unwrap();
			let b = GG::new_variable(ark_relations::ns!(cs, "generate_b"), || Ok(b_native), mode)
				.unwrap();

			let zero = GG::zero();
			assert_eq!(zero.value()?, zero.value()?);

			// a == a
			assert_eq!(a.value()?, a.value()?);
			// a + 0 = a
			assert_eq!((&a + &zero).value()?, a.value()?);
			// a - 0 = a
			assert_eq!((&a - &zero).value()?, a.value()?);
			// a - a = 0
			assert_eq!((&a - &a).value()?, zero.value()?);
			// a + b = b + a
			let a_b = &a + &b;
			let b_a = &b + &a;
			assert_eq!(a_b.value()?, b_a.value()?);
			a_b.enforce_equal(&b_a)?;
			assert!(cs.is_satisfied().unwrap());

			// (a + b) + a = a + (b + a)
			let ab_a = &a_b + &a;
			let a_ba = &a + &b_a;
			assert_eq!(ab_a.value()?, a_ba.value()?);
			ab_a.enforce_equal(&a_ba)?;
			assert!(cs.is_satisfied().unwrap());

			// a.double() = a + a
			let a_a = &a + &a;
			let mut a2 = a.clone();
			a2.double_in_place()?;
			a2.enforce_equal(&a_a)?;
			assert_eq!(a2.value()?, a_native.double());
			assert_eq!(a_a.value()?, a_native.double());
			assert_eq!(a2.value()?, a_a.value()?);
			assert!(cs.is_satisfied().unwrap());

			// b.double() = b + b
			let mut b2 = b.clone();
			b2.double_in_place()?;
			let b_b = &b + &b;
			b2.enforce_equal(&b_b)?;
			assert!(cs.is_satisfied().unwrap());
			assert_eq!(b2.value()?, b_b.value()?);

			let _ = a.to_bytes()?;
			assert!(cs.is_satisfied().unwrap());
			let _ = a.to_non_unique_bytes()?;
			assert!(cs.is_satisfied().unwrap());

			let _ = b.to_bytes()?;
			let _ = b.to_non_unique_bytes()?;
			if !cs.is_satisfied().unwrap() {
				panic!("Unsatisfied in mode {:?}.\n{:?}", mode, cs.which_is_unsatisfied().unwrap());
			}
			assert!(cs.is_satisfied().unwrap());

			let modulus = <C::ScalarField as PrimeField>::MODULUS.as_ref().to_vec();
			let mut max = modulus.clone();
			for limb in &mut max {
				*limb = u64::MAX;
			}

			let modulus_num_bits_mod_64 = <C::ScalarField as PrimeField>::MODULUS_BIT_SIZE % 64;
			if modulus_num_bits_mod_64 != 0 {
				*max.last_mut().unwrap() >>= 64 - modulus_num_bits_mod_64;
			}
			let scalars = [
				C::ScalarField::rand(&mut rng).into_bigint().as_ref().to_vec(),
				vec![u64::rand(&mut rng)],
				(-C::ScalarField::one()).into_bigint().as_ref().to_vec(),
				<C::ScalarField as PrimeField>::MODULUS.as_ref().to_vec(),
				max,
				vec![0; 50],
				vec![1000012341233u64; 36],
			];

			let mut input = vec![];

			// Check scalar mul with edge cases
			for scalar in scalars.iter() {
				let native_result = a_native.mul_bigint(scalar);
				let native_result = native_result.into_affine();

				let scalar_bits: Vec<bool> = BitIteratorLE::new(&scalar).collect();
				input =
					Vec::new_witness(ark_relations::ns!(cs, "bits"), || Ok(scalar_bits)).unwrap();
				let result = a.scalar_mul_le(input.iter()).expect(&format!("Mode: {:?}", mode));
				let result_val = result.value()?.into_affine();
				assert_eq!(
					result_val, native_result,
					"gadget & native values are diff. after scalar mul {:?}",
					scalar,
				);
				assert!(cs.is_satisfied().unwrap());
			}

			let result = zero.scalar_mul_le(input.iter())?;
			let result_val = result.value()?.into_affine();
			result.enforce_equal(&zero)?;
			assert_eq!(
				result_val,
				C::zero().into_affine(),
				"gadget & native values are diff. after scalar mul of zero"
			);
			assert!(cs.is_satisfied().unwrap());
		}
		Ok(())
	}

	pub fn sw_test<P, GG>() -> Result<(), SynthesisError>
	where
		P: ark_ec::models::short_weierstrass::SWCurveConfig,
		GG: CurveVar<SWProjective<P>, <P::BaseField as Field>::BasePrimeField>,
		for<'a> &'a GG: GroupOpsBounds<'a, SWProjective<P>, GG>,
	{
		group_test::<SWProjective<P>, _, GG>()?;
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let mut rng = test_rng();

			let cs = ConstraintSystem::<<P::BaseField as Field>::BasePrimeField>::new_ref();

			let a = SWProjective::<P>::rand(&mut rng);
			let b = SWProjective::<P>::rand(&mut rng);
			let a_affine = a.into_affine();
			let b_affine = b.into_affine();

			let ns = ark_relations::ns!(cs, "allocating variables");
			let mut gadget_a = GG::new_variable(cs.clone(), || Ok(a), mode)?;
			let gadget_b = GG::new_variable(cs.clone(), || Ok(b), mode)?;
			let zero = GG::zero();
			drop(ns);
			assert_eq!(gadget_a.value()?.into_affine().x, a_affine.x);
			assert_eq!(gadget_a.value()?.into_affine().y, a_affine.y);
			assert_eq!(gadget_b.value()?.into_affine().x, b_affine.x);
			assert_eq!(gadget_b.value()?.into_affine().y, b_affine.y);
			assert_eq!(cs.which_is_unsatisfied().unwrap(), None);

			// Check addition
			let ab = a + &b;
			let ab_affine = ab.into_affine();
			let gadget_ab = &gadget_a + &gadget_b;
			let gadget_ba = &gadget_b + &gadget_a;
			gadget_ba.enforce_equal(&gadget_ab)?;

			let ab_val = gadget_ab.value()?.into_affine();
			assert_eq!(ab_val, ab_affine, "Result of addition is unequal");
			assert!(cs.is_satisfied().unwrap());

			let gadget_a_zero = &gadget_a + &zero;
			gadget_a_zero.enforce_equal(&gadget_a)?;

			// Check doubling
			let aa = &a.double();
			let aa_affine = aa.into_affine();
			gadget_a.double_in_place()?;
			let aa_val = gadget_a.value()?.into_affine();
			assert_eq!(aa_val, aa_affine, "Gadget and native values are unequal after double.");
			assert!(cs.is_satisfied().unwrap());

			if !cs.is_satisfied().unwrap() {
				panic!("Unsatisfied in mode {:?}.\n{:?}", mode, cs.which_is_unsatisfied().unwrap());
			}

			assert!(cs.is_satisfied().unwrap());
		}
		Ok(())
	}

	pub fn te_test<P, GG>() -> Result<(), SynthesisError>
	where
		P: ark_ec::twisted_edwards::TECurveConfig,
		GG: CurveVar<TEProjective<P>, <P::BaseField as Field>::BasePrimeField>,
		for<'a> &'a GG: GroupOpsBounds<'a, TEProjective<P>, GG>,
	{
		group_test::<TEProjective<P>, _, GG>()?;
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let mut rng = test_rng();

			let cs = ConstraintSystem::<<P::BaseField as Field>::BasePrimeField>::new_ref();

			let a = TEProjective::<P>::rand(&mut rng);
			let b = TEProjective::<P>::rand(&mut rng);
			let a_affine = a.into_affine();
			let b_affine = b.into_affine();

			let ns = ark_relations::ns!(cs, "allocating variables");
			let mut gadget_a = GG::new_variable(cs.clone(), || Ok(a), mode)?;
			let gadget_b = GG::new_variable(cs.clone(), || Ok(b), mode)?;
			drop(ns);

			assert_eq!(gadget_a.value()?.into_affine().x, a_affine.x);
			assert_eq!(gadget_a.value()?.into_affine().y, a_affine.y);
			assert_eq!(gadget_b.value()?.into_affine().x, b_affine.x);
			assert_eq!(gadget_b.value()?.into_affine().y, b_affine.y);
			assert_eq!(cs.which_is_unsatisfied()?, None);

			// Check addition
			let ab = a + &b;
			let ab_affine = ab.into_affine();
			let gadget_ab = &gadget_a + &gadget_b;
			let gadget_ba = &gadget_b + &gadget_a;
			gadget_ba.enforce_equal(&gadget_ab)?;

			let ab_val = gadget_ab.value()?.into_affine();
			assert_eq!(ab_val, ab_affine, "Result of addition is unequal");
			assert!(cs.is_satisfied().unwrap());

			// Check doubling
			let aa = &a.double();
			let aa_affine = aa.into_affine();
			gadget_a.double_in_place()?;
			let aa_val = gadget_a.value()?.into_affine();
			assert_eq!(aa_val, aa_affine, "Gadget and native values are unequal after double.");
			assert!(cs.is_satisfied().unwrap());

			if !cs.is_satisfied().unwrap() {
				panic!("Unsatisfied in mode {:?}.\n{:?}", mode, cs.which_is_unsatisfied().unwrap());
			}

			assert!(cs.is_satisfied().unwrap());
		}
		Ok(())
	}
}

pub mod pairing {
	use ark_ec::{
		pairing::{Pairing, PairingOutput},
		AffineRepr, CurveGroup,
	};
	use ark_ff::{BitIteratorLE, Field, PrimeField};
	use ark_r1cs_std::prelude::*;
	use ark_relations::r1cs::{ConstraintSystem, SynthesisError};
	use ark_std::{test_rng, vec::Vec, UniformRand};

	#[allow(dead_code)]
	pub fn bilinearity_test<E: Pairing, P: PairingVar<E>>() -> Result<(), SynthesisError>
	where
		for<'a> &'a P::G1Var: GroupOpsBounds<'a, E::G1, P::G1Var>,
		for<'a> &'a P::G2Var: GroupOpsBounds<'a, E::G2, P::G2Var>,
		for<'a> &'a P::GTVar: FieldOpsBounds<'a, E::TargetField, P::GTVar>,
	{
		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let cs = ConstraintSystem::<<E::G1 as CurveGroup>::BaseField>::new_ref();

			let mut rng = test_rng();
			let a = E::G1::rand(&mut rng);
			let b = E::G2::rand(&mut rng);
			let s = E::ScalarField::rand(&mut rng);

			let mut sa = a;
			sa *= s;
			let mut sb = b;
			sb *= s;

			let a_g = P::G1Var::new_variable(cs.clone(), || Ok(a.into_affine()), mode)?;
			let b_g = P::G2Var::new_variable(cs.clone(), || Ok(b.into_affine()), mode)?;
			let sa_g = P::G1Var::new_variable(cs.clone(), || Ok(sa.into_affine()), mode)?;
			let sb_g = P::G2Var::new_variable(cs.clone(), || Ok(sb.into_affine()), mode)?;

			let mut _preparation_num_constraints = cs.num_constraints();
			let a_prep_g = P::prepare_g1(&a_g)?;
			let b_prep_g = P::prepare_g2(&b_g)?;
			_preparation_num_constraints = cs.num_constraints() - _preparation_num_constraints;

			let sa_prep_g = P::prepare_g1(&sa_g)?;
			let sb_prep_g = P::prepare_g2(&sb_g)?;

			let (ans1_g, ans1_n) = {
				let _ml_constraints = cs.num_constraints();
				let ml_g = P::miller_loop(&[sa_prep_g], &[b_prep_g.clone()])?;
				let _fe_constraints = cs.num_constraints();
				let ans_g = P::final_exponentiation(&ml_g)?;
				let ans_n = E::pairing(sa, b);
				(ans_g, ans_n)
			};

			let (ans2_g, ans2_n) = {
				let ans_g = P::pairing(a_prep_g.clone(), sb_prep_g)?;
				let ans_n = E::pairing(a, sb);
				(ans_g, ans_n)
			};

			let (ans3_g, ans3_n) = {
				let s_iter = BitIteratorLE::without_trailing_zeros(s.into_bigint())
					.map(Boolean::constant)
					.collect::<Vec<_>>();

				let mut ans_g = P::pairing(a_prep_g, b_prep_g)?;
				let mut ans_n = E::pairing(a, b);
				ans_n = PairingOutput(ans_n.0.pow(s.into_bigint()));
				ans_g = ans_g.pow_le(&s_iter)?;

				(ans_g, ans_n)
			};

			ans1_g.enforce_equal(&ans2_g)?;
			ans2_g.enforce_equal(&ans3_g)?;

			assert_eq!(ans1_g.value()?, ans1_n.0, "Failed native test 1");
			assert_eq!(ans2_g.value()?, ans2_n.0, "Failed native test 2");
			assert_eq!(ans3_g.value()?, ans3_n.0, "Failed native test 3");

			assert_eq!(ans1_n.0, ans2_n.0, "Failed ans1_native == ans2_native");
			assert_eq!(ans2_n.0, ans3_n.0, "Failed ans2_native == ans3_native");
			assert_eq!(ans1_g.value()?, ans3_g.value()?, "Failed ans1 == ans3");
			assert_eq!(ans1_g.value()?, ans2_g.value()?, "Failed ans1 == ans2");
			assert_eq!(ans2_g.value()?, ans3_g.value()?, "Failed ans2 == ans3");

			if !cs.is_satisfied().unwrap() {
				panic!("Unsatisfied in mode {:?}.\n{:?}", mode, cs.which_is_unsatisfied().unwrap());
			}

			assert!(cs.is_satisfied().unwrap(), "cs is not satisfied");
		}
		Ok(())
	}

	#[allow(dead_code)]
	pub fn g2_prepare_consistency_test<E: Pairing, P: PairingVar<E>>() -> Result<(), SynthesisError>
	{
		let test_g2_elem = E::G2Affine::generator();
		let test_g2_prepared = E::G2Prepared::from(test_g2_elem.clone());

		let modes = [AllocationMode::Input, AllocationMode::Witness, AllocationMode::Constant];
		for &mode in &modes {
			let cs = ConstraintSystem::new_ref();

			let test_g2_gadget =
				P::G2Var::new_witness(cs.clone(), || Ok(test_g2_elem.clone())).unwrap();

			let prepared_test_g2_gadget = P::prepare_g2(&test_g2_gadget).unwrap();
			let allocated_test_g2_gadget =
				P::G2PreparedVar::new_variable(cs.clone(), || Ok(test_g2_prepared.clone()), mode)
					.unwrap();

			let prepared_test_g2_gadget_bytes = prepared_test_g2_gadget.to_bytes().unwrap();
			let allocated_test_g2_gadget_bytes = allocated_test_g2_gadget.to_bytes().unwrap();

			prepared_test_g2_gadget_bytes
				.enforce_equal(&allocated_test_g2_gadget_bytes)
				.unwrap();

			assert!(cs.is_satisfied().unwrap(), "cs is not satisfied");
		}
		Ok(())
	}
}
