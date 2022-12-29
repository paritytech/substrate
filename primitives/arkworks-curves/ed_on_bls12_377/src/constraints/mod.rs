//! This module implements the R1CS equivalent of `ark_ed_on_bls12_377`.
//!
//! It implements field variables for `crate::Fq`,
//! and group variables for `crate::Projective`.
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
//! use ark_ed_on_bls12_377::{*, constraints::*};
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
//! One can also perform standard algebraic operations on `EdwardsVar`:
//!
//! ```
//! # fn main() -> Result<(), ark_relations::r1cs::SynthesisError> {
//! # use ark_std::UniformRand;
//! # use ark_relations::r1cs::*;
//! # use ark_r1cs_std::prelude::*;
//! # use ark_ed_on_bls12_377::{*, constraints::*};
//!
//! # let cs = ConstraintSystem::<Fq>::new_ref();
//! # let mut rng = ark_std::test_rng();
//!
//! // Generate some random `Edwards` elements.
//! let a_native = EdwardsProjective::rand(&mut rng);
//! let b_native = EdwardsProjective::rand(&mut rng);
//!
//! // Allocate `a_native` and `b_native` as witness variables in `cs`.
//! let a = EdwardsVar::new_witness(ark_relations::ns!(cs, "a"), || Ok(a_native))?;
//! let b = EdwardsVar::new_witness(ark_relations::ns!(cs, "b"), || Ok(b_native))?;
//!
//! // Allocate `a_native` and `b_native` as constants in `cs`. This does not add any
//! // constraints or variables.
//! let a_const = EdwardsVar::new_constant(ark_relations::ns!(cs, "a_as_constant"), a_native)?;
//! let b_const = EdwardsVar::new_constant(ark_relations::ns!(cs, "b_as_constant"), b_native)?;
//!
//! // This returns the identity.
//! let zero = EdwardsVar::zero();
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

mod curves;
mod fields;

pub use curves::*;
pub use fields::*;
