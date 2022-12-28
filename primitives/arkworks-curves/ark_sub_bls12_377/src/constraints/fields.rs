use ark_r1cs_std::fields::{fp::FpVar, fp12::Fp12Var, fp2::Fp2Var, fp6_3over2::Fp6Var};

use crate::{Fq, Fq12Config, Fq2Config, Fq6Config};

/// A variable that is the R1CS equivalent of `crate::Fq`.
pub type FqVar = FpVar<Fq>;

/// A variable that is the R1CS equivalent of `crate::Fq2`.
pub type Fq2Var = Fp2Var<Fq2Config>;
/// A variable that is the R1CS equivalent of `crate::Fq6`.
pub type Fq6Var = Fp6Var<Fq6Config>;
/// A variable that is the R1CS equivalent of `crate::Fq12`.
pub type Fq12Var = Fp12Var<Fq12Config>;

#[test]
fn bls12_377_field_test() {
    use super::*;
    use crate::{Fq, Fq12, Fq2, Fq6};
    use ark_curve_constraint_tests::fields::*;

    field_test::<_, _, FqVar>().unwrap();
    frobenius_tests::<Fq, _, FqVar>(13).unwrap();

    field_test::<_, _, Fq2Var>().unwrap();
    frobenius_tests::<Fq2, _, Fq2Var>(13).unwrap();

    field_test::<_, _, Fq6Var>().unwrap();
    frobenius_tests::<Fq6, _, Fq6Var>(13).unwrap();

    field_test::<_, _, Fq12Var>().unwrap();
    frobenius_tests::<Fq12, _, Fq12Var>(13).unwrap();
}
