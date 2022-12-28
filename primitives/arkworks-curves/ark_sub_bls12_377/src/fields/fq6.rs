use ark_ff::{fields::*, MontFp};

use crate::*;

pub type Fq6 = Fp6<Fq6Config>;

#[derive(Clone, Copy)]
pub struct Fq6Config;

impl Fp6Config for Fq6Config {
    type Fp2Config = Fq2Config;

    /// NONRESIDUE = U
    const NONRESIDUE: Fq2 = Fq2::new(Fq::ZERO, Fq::ONE);

    const FROBENIUS_COEFF_FP6_C1: &'static [Fq2] = &[
        // Fp2::NONRESIDUE^(((q^0) - 1) / 3)
        Fq2::new(Fq::ONE, Fq::ZERO),
        // Fp2::NONRESIDUE^(((q^1) - 1) / 3)
        Fq2::new(
            MontFp!("80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410946"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^2) - 1) / 3)
        Fq2::new(
            MontFp!("80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^3) - 1) / 3)
        Fq2::new(MontFp!("-1"), Fq::ZERO),
        // Fp2::NONRESIDUE^(((q^4) - 1) / 3)
        Fq2::new(
            MontFp!("258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047231"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^(((q^5) - 1) / 3)
        Fq2::new(
            MontFp!("258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047232"),
            Fq::ZERO,
        ),
    ];

    const FROBENIUS_COEFF_FP6_C2: &'static [Fq2] = &[
        // Fp2::NONRESIDUE^((2*(q^0) - 2) / 3)
        Fq2::new(Fq::ONE, Fq::ZERO),
        // Fp2::NONRESIDUE^((2*(q^1) - 2) / 3)
        Fq2::new(
            MontFp!("80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945"),
            Fq::ZERO
        ),
        // Fp2::NONRESIDUE^((2*(q^2) - 2) / 3)
        Fq2::new(
            MontFp!("258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047231"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^((2*(q^3) - 2) / 3)
        Fq2::new(Fq::ONE, Fq::ZERO),
        // Fp2::NONRESIDUE^((2*(q^4) - 2) / 3)
        Fq2::new(
            MontFp!("80949648264912719408558363140637477264845294720710499478137287262712535938301461879813459410945"),
            Fq::ZERO,
        ),
        // Fp2::NONRESIDUE^((2*(q^5) - 2) / 3)
        Fq2::new(
            MontFp!("258664426012969093929703085429980814127835149614277183275038967946009968870203535512256352201271898244626862047231"),
            Fq::ZERO,
        ),
    ];

    #[inline(always)]
    fn mul_fp2_by_nonresidue_in_place(fe: &mut Fq2) -> &mut Fq2 {
        // Karatsuba multiplication with constant other = u.
        let old_c0 = fe.c0;
        fe.c0 = fe.c1;
        Fq2Config::mul_fp_by_nonresidue_in_place(&mut fe.c0);
        fe.c1 = old_c0;
        fe
    }
}
