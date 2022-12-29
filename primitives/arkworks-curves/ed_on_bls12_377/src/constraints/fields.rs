use ark_r1cs_std::fields::fp::FpVar;

use crate::fq::Fq;

/// A variable that is the R1CS equivalent of `crate::Fq`.
pub type FqVar = FpVar<Fq>;

#[test]
fn test() {
    ark_curve_constraint_tests::fields::field_test::<_, _, FqVar>().unwrap();
}
