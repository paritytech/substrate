use ark_ff::{fields::*, MontFp};

use crate::*;

pub type Fq2 = Fp2<Fq2Config>;

pub struct Fq2Config;

impl Fp2Config for Fq2Config {
    type Fp = Fq;

    /// NONRESIDUE = -5
    const NONRESIDUE: Fq = MontFp!("-5");

    /// Coefficients for the Frobenius automorphism.
    const FROBENIUS_COEFF_FP2_C1: &'static [Fq] = &[
        // NONRESIDUE**(((q^0) - 1) / 2)
        Fq::ONE,
        // NONRESIDUE**(((q^1) - 1) / 2)
        MontFp!("-1"),
    ];

    #[inline(always)]
    fn mul_fp_by_nonresidue_in_place(fe: &mut Self::Fp) -> &mut Self::Fp {
        fe.neg_in_place();
        *fe = *fe + fe.double_in_place().double_in_place();
        fe
    }

    #[inline(always)]
    fn sub_and_mul_fp_by_nonresidue(y: &mut Self::Fp, x: &Self::Fp) {
        let mut original = *y;
        original += x;
        y.double_in_place().double_in_place();
        *y += original;
    }

    #[inline(always)]
    fn mul_fp_by_nonresidue_plus_one_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        y.double_in_place().double_in_place().neg_in_place();
        *y += x;
    }

    fn mul_fp_by_nonresidue_and_add(y: &mut Self::Fp, x: &Self::Fp) {
        let mut original = *y;
        original.double_in_place().double_in_place();
        original += &*y;
        *y = *x;
        *y -= original;
    }
}
