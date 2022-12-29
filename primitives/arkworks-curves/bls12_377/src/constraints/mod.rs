//! This module implements the R1CS equivalent of `crate`.
//!
//! It implements field variables for `crate::{Fq, Fq2, Fq6, Fq12}`,
//! group variables for `crate::{G1, G2}`, and implements constraint
//! generation for computing `Bls12_377::pairing`.
//!
//! The field underlying these constraints is `crate::Fq`.
//!
//! # Examples
//!
//! One can perform standard algebraic operations on `FqVar`:
//!
//! ```
//! # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
//! use ark_std::UniformRand;
//! use ark_relations::r1cs::*;
//! use ark_r1cs_std::prelude::*;
//! use ark_bls12_377::{*, constraints::*};
//!
//! let cs = ConstraintSystem::<Fq>::new_ref();
//! // This rng is just for test purposes; do not use it
//! // in real applications.
//! let mut rng = ark_std::test_rng();
//!
//! // Generate some random `Fq` elements.
//! let a_native = Fq::rand(&mut rng);
//! let b_native = Fq::rand(&mut rng);
//!
//! // Allocate `a_native` and `b_native` as witness variables in `cs`.
//! let a = FqVar::new_witness(ark_relations::ns!(cs, "generate_a"), || Ok(a_native))?;
//! let b = FqVar::new_witness(ark_relations::ns!(cs, "generate_b"), || Ok(b_native))?;
//!
//! // Allocate `a_native` and `b_native` as constants in `cs`. This does not add any
//! // constraints or variables.
//! let a_const = FqVar::new_constant(ark_relations::ns!(cs, "a_as_constant"), a_native)?;
//! let b_const = FqVar::new_constant(ark_relations::ns!(cs, "b_as_constant"), b_native)?;
//!
//! let one = FqVar::one();
//! let zero = FqVar::zero();
//!
//! // Sanity check one + one = two
//! let two = &one + &one + &zero;
//! two.enforce_equal(&one.double()?)?;
//!
//! assert!(cs.is_satisfied()?);
//!
//! // Check that the value of &a + &b is correct.
//! assert_eq!((&a + &b).value()?, a_native + &b_native);
//!
//! // Check that the value of &a * &b is correct.
//! assert_eq!((&a * &b).value()?, a_native * &b_native);
//!
//! // Check that operations on variables and constants are equivalent.
//! (&a + &b).enforce_equal(&(&a_const + &b_const))?;
//! assert!(cs.is_satisfied()?);
//! # Ok(())
//! # }
//! ```
//!
//! One can also perform standard algebraic operations on `G1Var` and `G2Var`:
//!
//! ```
//! # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
//! # use ark_std::UniformRand;
//! # use ark_relations::r1cs::*;
//! # use ark_r1cs_std::prelude::*;
//! # use ark_bls12_377::{*, constraints::*};
//!
//! # let cs = ConstraintSystem::<Fq>::new_ref();
//! # let mut rng = ark_std::test_rng();
//!
//! // Generate some random `G1` elements.
//! let a_native = G1Projective::rand(&mut rng);
//! let b_native = G1Projective::rand(&mut rng);
//!
//! // Allocate `a_native` and `b_native` as witness variables in `cs`.
//! let a = G1Var::new_witness(ark_relations::ns!(cs, "a"), || Ok(a_native))?;
//! let b = G1Var::new_witness(ark_relations::ns!(cs, "b"), || Ok(b_native))?;
//!
//! // Allocate `a_native` and `b_native` as constants in `cs`. This does not add any
//! // constraints or variables.
//! let a_const = G1Var::new_constant(ark_relations::ns!(cs, "a_as_constant"), a_native)?;
//! let b_const = G1Var::new_constant(ark_relations::ns!(cs, "b_as_constant"), b_native)?;
//!
//! // This returns the identity of `G1`.
//! let zero = G1Var::zero();
//!
//! // Sanity check one + one = two
//! let two_a = &a + &a + &zero;
//! two_a.enforce_equal(&a.double()?)?;
//!
//! assert!(cs.is_satisfied()?);
//!
//! // Check that the value of &a + &b is correct.
//! assert_eq!((&a + &b).value()?, a_native + &b_native);
//!
//! // Check that operations on variables and constants are equivalent.
//! (&a + &b).enforce_equal(&(&a_const + &b_const))?;
//! assert!(cs.is_satisfied()?);
//! # Ok(())
//! # }
//! ```
//!
//! Finally, one can check pairing computations as well:
//!
//! ```
//! # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
//! # use ark_std::UniformRand;
//! # use ark_ec::pairing::Pairing;
//! # use ark_relations::r1cs::*;
//! # use ark_r1cs_std::prelude::*;
//! # use ark_bls12_377::{*, constraints::*};
//!
//! # let cs = ConstraintSystem::<Fq>::new_ref();
//! # let mut rng = ark_std::test_rng();
//!
//! // Generate random `G1` and `G2` elements.
//! let a_native = G1Projective::rand(&mut rng);
//! let b_native = G2Projective::rand(&mut rng);
//!
//! // Allocate `a_native` and `b_native` as witness variables in `cs`.
//! let a = G1Var::new_witness(ark_relations::ns!(cs, "a"), || Ok(a_native))?;
//! let b = G2Var::new_witness(ark_relations::ns!(cs, "b"), || Ok(b_native))?;
//!
//! // Allocate `a_native` and `b_native` as constants in `cs`. This does not add any
//! // constraints or variables.
//! let a_const = G1Var::new_constant(ark_relations::ns!(cs, "a_as_constant"), a_native)?;
//! let b_const = G2Var::new_constant(ark_relations::ns!(cs, "b_as_constant"), b_native)?;
//!
//! let pairing_result_native = Bls12_377::pairing(a_native, b_native);
//!
//! // Prepare `a` and `b` for pairing.
//! let a_prep = constraints::PairingVar::prepare_g1(&a)?;
//! let b_prep = constraints::PairingVar::prepare_g2(&b)?;
//! let pairing_result = constraints::PairingVar::pairing(a_prep, b_prep)?;
//!
//! // Check that the value of &a + &b is correct.
//! assert_eq!(pairing_result.value()?, pairing_result_native.0);
//!
//! // Check that operations on variables and constants are equivalent.
//! let a_prep_const = constraints::PairingVar::prepare_g1(&a_const)?;
//! let b_prep_const = constraints::PairingVar::prepare_g2(&b_const)?;
//! let pairing_result_const = constraints::PairingVar::pairing(a_prep_const, b_prep_const)?;
//! println!("Done here 3");
//!
//! pairing_result.enforce_equal(&pairing_result_const)?;
//! assert!(cs.is_satisfied()?);
//! # Ok(())
//! # }
//! ```

mod fields;
pub use fields::*;

#[cfg(feature = "curve")]
mod curves;
#[cfg(feature = "curve")]
mod pairing;

#[cfg(feature = "curve")]
pub use curves::*;
#[cfg(feature = "curve")]
pub use pairing::*;
