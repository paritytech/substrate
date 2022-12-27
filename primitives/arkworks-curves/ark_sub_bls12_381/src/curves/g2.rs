use ark_ec::{
    models::{short_weierstrass::SWCurveConfig, CurveConfig},
    short_weierstrass::Affine,
};
use ark_ff::{Field, MontFp, Zero};

use crate::{g1, Fq, Fq2, Fr};

pub type G2Affine = Affine<Config>;
#[derive(Clone, Default, PartialEq, Eq)]
pub struct Config;

impl CurveConfig for Config {
    type BaseField = Fq2;
    type ScalarField = Fr;

    /// COFACTOR =
    /// 7923214915284317143930293550643874566881017850177945424769256759165301436616933228209277966774092486467289478618404761412630691835764674559376407658497
    #[rustfmt::skip]
    const COFACTOR: &'static [u64] = &[
        0x0000000000000001,
        0x452217cc90000000,
        0xa0f3622fba094800,
        0xd693e8c36676bd09,
        0x8c505634fae2e189,
        0xfbb36b00e1dcc40c,
        0xddd88d99a6f6a829,
        0x26ba558ae9562a,
    ];

    /// COFACTOR_INV = COFACTOR^{-1} mod r
    /// = 6764900296503390671038341982857278410319949526107311149686707033187604810669
    const COFACTOR_INV: Fr =
        MontFp!("6764900296503390671038341982857278410319949526107311149686707033187604810669");
}

impl SWCurveConfig for Config {
    /// COEFF_A = [0, 0]
    const COEFF_A: Fq2 = Fq2::new(g1::Config::COEFF_A, g1::Config::COEFF_A);

    // As per https://eprint.iacr.org/2012/072.pdf,
    // this curve has b' = b/i, where b is the COEFF_B of G1, and x^6 -i is
    // the irreducible poly used to extend from Fp2 to Fp12.
    // In our case, i = u (App A.3, T_6).
    /// COEFF_B = [0,
    /// 155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906]
    const COEFF_B: Fq2 = Fq2::new(
        Fq::ZERO,
        MontFp!("155198655607781456406391640216936120121836107652948796323930557600032281009004493664981332883744016074664192874906"),
    );

    /// AFFINE_GENERATOR_COEFFS = (G2_GENERATOR_X, G2_GENERATOR_Y)
    const GENERATOR: G2Affine = G2Affine::new_unchecked(G2_GENERATOR_X, G2_GENERATOR_Y);

    #[inline(always)]
    fn mul_by_a(_: Self::BaseField) -> Self::BaseField {
        Self::BaseField::zero()
    }

    /// Default implementation of group multiplication for projective
    /// coordinates
    fn mul_projective(base: &Projective<Self>, scalar: &[u64]) -> Projective<Self> {
        let mut res = Projective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base;
            }
        }

        res
    }

    /// Default implementation of group multiplication for affine
    /// coordinates.
    fn mul_affine(base: &Affine<Self>, scalar: &[u64]) -> Projective<Self> {
        let mut res = Projective::<Self>::zero();
        for b in ark_ff::BitIteratorBE::without_leading_zeros(scalar) {
            res.double_in_place();
            if b {
                res += base
            }
        }

        res
    }

    /// Default implementation for multi scalar multiplication
    fn msm(
        bases: &[Affine<Self>],
        scalars: &[Self::ScalarField],
    ) -> Result<Projective<Self>, usize> {
        (bases.len() == scalars.len())
            .then(|| VariableBaseMSM::msm_unchecked(bases, scalars))
            .ok_or(usize::min(bases.len(), scalars.len()))
    }

}

pub const G2_GENERATOR_X: Fq2 = Fq2::new(G2_GENERATOR_X_C0, G2_GENERATOR_X_C1);
pub const G2_GENERATOR_Y: Fq2 = Fq2::new(G2_GENERATOR_Y_C0, G2_GENERATOR_Y_C1);

/// G2_GENERATOR_X_C0 =
/// 233578398248691099356572568220835526895379068987715365179118596935057653620464273615301663571204657964920925606294
pub const G2_GENERATOR_X_C0: Fq = MontFp!("233578398248691099356572568220835526895379068987715365179118596935057653620464273615301663571204657964920925606294");

/// G2_GENERATOR_X_C1 =
/// 140913150380207355837477652521042157274541796891053068589147167627541651775299824604154852141315666357241556069118
pub const G2_GENERATOR_X_C1: Fq = MontFp!("140913150380207355837477652521042157274541796891053068589147167627541651775299824604154852141315666357241556069118");

/// G2_GENERATOR_Y_C0 =
/// 63160294768292073209381361943935198908131692476676907196754037919244929611450776219210369229519898517858833747423
pub const G2_GENERATOR_Y_C0: Fq = MontFp!("63160294768292073209381361943935198908131692476676907196754037919244929611450776219210369229519898517858833747423");

/// G2_GENERATOR_Y_C1 =
/// 149157405641012693445398062341192467754805999074082136895788947234480009303640899064710353187729182149407503257491
pub const G2_GENERATOR_Y_C1: Fq = MontFp!("149157405641012693445398062341192467754805999074082136895788947234480009303640899064710353187729182149407503257491");
