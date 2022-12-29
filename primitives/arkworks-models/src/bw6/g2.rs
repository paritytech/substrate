use ark_ff::{BitIteratorBE, Field};
use ark_serialize::*;
use ark_std::vec::Vec;
use num_traits::One;

use crate::{
    bw6::{BW6Config, TwistType},
    models::short_weierstrass::SWCurveConfig,
    short_weierstrass::{Affine, Projective},
    AffineRepr, CurveGroup,
};

pub type G2Affine<P> = Affine<<P as BW6Config>::G2Config>;
pub type G2Projective<P> = Projective<<P as BW6Config>::G2Config>;

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: BW6Config"),
    Debug(bound = "P: BW6Config"),
    PartialEq(bound = "P: BW6Config"),
    Eq(bound = "P: BW6Config")
)]
pub struct G2Prepared<P: BW6Config> {
    // Stores the coefficients of the line evaluations as calculated in
    // https://eprint.iacr.org/2013/722.pdf
    pub ell_coeffs_1: Vec<(P::Fp, P::Fp, P::Fp)>,
    pub ell_coeffs_2: Vec<(P::Fp, P::Fp, P::Fp)>,
    pub infinity: bool,
}

#[derive(Derivative, CanonicalSerialize, CanonicalDeserialize)]
#[derivative(
    Clone(bound = "P: BW6Config"),
    Copy(bound = "P: BW6Config"),
    Debug(bound = "P: BW6Config")
)]
struct G2HomProjective<P: BW6Config> {
    x: P::Fp,
    y: P::Fp,
    z: P::Fp,
}

impl<P: BW6Config> Default for G2Prepared<P> {
    fn default() -> Self {
        Self::from(G2Affine::<P>::generator())
    }
}

impl<P: BW6Config> From<G2Affine<P>> for G2Prepared<P> {
    fn from(q: G2Affine<P>) -> Self {
        if q.infinity {
            return Self {
                ell_coeffs_1: vec![],
                ell_coeffs_2: vec![],
                infinity: true,
            };
        }

        // f_{u+1,Q}(P)
        let mut ell_coeffs_1 = vec![];
        let mut r = G2HomProjective::<P> {
            x: q.x,
            y: q.y,
            z: P::Fp::one(),
        };

        for i in BitIteratorBE::new(P::ATE_LOOP_COUNT_1).skip(1) {
            ell_coeffs_1.push(r.double_in_place());

            if i {
                ell_coeffs_1.push(r.add_in_place(&q));
            }
        }

        // f_{u^3-u^2-u,Q}(P)
        let mut ell_coeffs_2 = vec![];
        let mut r = G2HomProjective::<P> {
            x: q.x,
            y: q.y,
            z: P::Fp::one(),
        };

        let negq = -q;

        for bit in P::ATE_LOOP_COUNT_2.iter().rev().skip(1) {
            ell_coeffs_2.push(r.double_in_place());

            match bit {
                1 => ell_coeffs_2.push(r.add_in_place(&q)),
                -1 => ell_coeffs_2.push(r.add_in_place(&negq)),
                _ => continue,
            }
        }

        Self {
            ell_coeffs_1,
            ell_coeffs_2,
            infinity: false,
        }
    }
}

impl<'a, P: BW6Config> From<&'a G2Affine<P>> for G2Prepared<P> {
    fn from(q: &'a G2Affine<P>) -> Self {
        (*q).into()
    }
}

impl<'a, P: BW6Config> From<&'a G2Projective<P>> for G2Prepared<P> {
    fn from(q: &'a G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> From<G2Projective<P>> for G2Prepared<P> {
    fn from(q: G2Projective<P>) -> Self {
        q.into_affine().into()
    }
}

impl<P: BW6Config> G2Prepared<P> {
    pub fn is_zero(&self) -> bool {
        self.infinity
    }
}

impl<P: BW6Config> G2HomProjective<P> {
    fn double_in_place(&mut self) -> (P::Fp, P::Fp, P::Fp) {
        // Formula for line function when working with
        // homogeneous projective coordinates, as described in https://eprint.iacr.org/2013/722.pdf.

        let a = self.x * &self.y;
        let b = self.y.square();
        let b4 = b.double().double();
        let c = self.z.square();
        let e = P::G2Config::COEFF_B * &(c.double() + &c);
        let f = e.double() + &e;
        let g = b + &f;
        let h = (self.y + &self.z).square() - &(b + &c);
        let i = e - &b;
        let j = self.x.square();
        let e2_square = e.double().square();

        self.x = a.double() * &(b - &f);
        self.y = g.square() - &(e2_square.double() + &e2_square);
        self.z = b4 * &h;
        match P::TWIST_TYPE {
            TwistType::M => (i, j.double() + &j, -h),
            TwistType::D => (-h, j.double() + &j, i),
        }
    }

    fn add_in_place(&mut self, q: &G2Affine<P>) -> (P::Fp, P::Fp, P::Fp) {
        // Formula for line function when working with
        // homogeneous projective coordinates, as described in https://eprint.iacr.org/2013/722.pdf.
        let theta = self.y - &(q.y * &self.z);
        let lambda = self.x - &(q.x * &self.z);
        let c = theta.square();
        let d = lambda.square();
        let e = lambda * &d;
        let f = self.z * &c;
        let g = self.x * &d;
        let h = e + &f - &g.double();
        self.x = lambda * &h;
        self.y = theta * &(g - &h) - &(e * &self.y);
        self.z *= &e;
        let j = theta * &q.x - &(lambda * &q.y);

        match P::TWIST_TYPE {
            TwistType::M => (j, -theta, lambda),
            TwistType::D => (lambda, -theta, j),
        }
    }
}
