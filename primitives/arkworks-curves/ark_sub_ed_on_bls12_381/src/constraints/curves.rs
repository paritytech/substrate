use ark_r1cs_std::groups::curves::{short_weierstrass::ProjectiveVar, twisted_edwards::AffineVar};

use crate::{constraints::FqVar, *};

/// A variable that is the R1CS equivalent of `crate::EdwardsAffine`.
pub type EdwardsVar = AffineVar<JubjubConfig, FqVar>;

/// A variable that is the R1CS equivalent of `crate::SWProjective`
pub type SWVar = ProjectiveVar<JubjubConfig, FqVar>;

#[test]
fn test() {
    ark_curve_constraint_tests::curves::te_test::<_, EdwardsVar>().unwrap();
    ark_curve_constraint_tests::curves::sw_test::<_, SWVar>().unwrap();
    ark_curve_constraint_tests::curves::group_test::<_, Fq, EdwardsVar>().unwrap();
}
