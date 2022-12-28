use ark_algebra_test_templates::*;
use ark_ff::{
    biginteger::{BigInt, BigInteger, BigInteger384},
    fields::{FftField, Field, Fp6Config, PrimeField},
    Fp384, One, UniformRand, Zero,
};
use ark_std::{
    cmp::Ordering,
    ops::{AddAssign, MulAssign},
    test_rng,
};

use crate::{Fq, Fq12, Fq2, Fq6, Fq6Config, Fr};

test_field!(fr; Fr; mont_prime_field);
test_field!(fq; Fq; mont_prime_field);
test_field!(fq2; Fq2);
test_field!(fq6; Fq6);
test_field!(fq12; Fq12);

#[test]
fn test_fq_repr_from() {
    assert_eq!(BigInt::from(100u64), BigInt::new([100, 0, 0, 0, 0, 0]));
}

#[test]
fn test_fq_repr_is_odd() {
    assert!(!BigInteger384::from(0u64).is_odd());
    assert!(BigInteger384::from(0u64).is_even());
    assert!(BigInteger384::from(1u64).is_odd());
    assert!(!BigInteger384::from(1u64).is_even());
    assert!(!BigInteger384::from(324834872u64).is_odd());
    assert!(BigInteger384::from(324834872u64).is_even());
    assert!(BigInteger384::from(324834873u64).is_odd());
    assert!(!BigInteger384::from(324834873u64).is_even());
}

#[test]
fn test_fq_repr_is_zero() {
    assert!(BigInteger384::from(0u64).is_zero());
    assert!(!BigInteger384::from(1u64).is_zero());
    assert!(!BigInt::new([0, 0, 0, 0, 1, 0]).is_zero());
}

#[test]
fn test_fq_repr_num_bits() {
    let mut a = BigInteger384::from(0u64);
    assert_eq!(0, a.num_bits());
    a = BigInteger384::from(1u64);
    for i in 1..385 {
        assert_eq!(i, a.num_bits());
        a.mul2();
    }
    assert_eq!(0, a.num_bits());
}

#[test]
fn test_fq_num_bits() {
    assert_eq!(Fq::MODULUS_BIT_SIZE, 377);
}

#[test]
fn test_fq_root_of_unity() {
    assert_eq!(Fq::TWO_ADICITY, 46);
    assert_eq!(
        Fq::GENERATOR.pow([
            0x7510c00000021423,
            0x88bee82520005c2d,
            0x67cc03d44e3c7bcd,
            0x1701b28524ec688b,
            0xe9185f1443ab18ec,
            0x6b8
        ]),
        Fq::TWO_ADIC_ROOT_OF_UNITY
    );
    assert_eq!(
        Fq::TWO_ADIC_ROOT_OF_UNITY.pow([1 << Fq::TWO_ADICITY]),
        Fq::one()
    );
    assert!(Fq::GENERATOR.sqrt().is_none());
}

#[test]
fn test_fq_ordering() {
    // BigInteger384's ordering is well-tested, but we still need to make sure the
    // Fq elements aren't being compared in Montgomery form.
    for i in 0..100u64 {
        assert!(Fq::from(Fp384::from(i + 1)) > Fq::from(Fp384::from(i)));
    }
}

#[test]
fn test_fq_legendre() {
    use ark_ff::fields::LegendreSymbol::*;

    assert_eq!(QuadraticResidue, Fq::one().legendre());
    assert_eq!(Zero, Fq::zero().legendre());
    assert_eq!(QuadraticResidue, Fq::from(Fp384::from(4u64)).legendre());
    assert_eq!(QuadraticNonResidue, Fq::from(Fp384::from(5u64)).legendre());
}

#[test]
fn test_fq2_ordering() {
    let mut a = Fq2::new(Fq::zero(), Fq::zero());
    let mut b = a.clone();

    assert!(a.cmp(&b) == Ordering::Equal);
    b.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Equal);
    b.c1.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Less);
    a.c1.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Greater);
    b.c0.add_assign(&Fq::one());
    assert!(a.cmp(&b) == Ordering::Equal);
}

#[test]
fn test_fq2_basics() {
    assert_eq!(Fq2::new(Fq::zero(), Fq::zero(),), Fq2::zero());
    assert_eq!(Fq2::new(Fq::one(), Fq::zero(),), Fq2::one());
    assert!(Fq2::zero().is_zero());
    assert!(!Fq2::one().is_zero());
    assert!(!Fq2::new(Fq::zero(), Fq::one(),).is_zero());
}

#[test]
fn test_fq2_legendre() {
    use ark_ff::fields::LegendreSymbol::*;

    assert_eq!(Zero, Fq2::zero().legendre());
    // i^2 = -1
    let mut m1 = -Fq2::one();
    assert_eq!(QuadraticResidue, m1.legendre());
    Fq6Config::mul_fp2_by_nonresidue_in_place(&mut m1);
    assert_eq!(QuadraticNonResidue, m1.legendre());
}

#[test]
fn test_fq6_mul_by_1() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c1 = Fq2::rand(&mut rng);
        let mut a = Fq6::rand(&mut rng);
        let mut b = a;

        a.mul_by_1(&c1);
        b.mul_assign(&Fq6::new(Fq2::zero(), c1, Fq2::zero()));

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq6_mul_by_01() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c1 = Fq2::rand(&mut rng);
        let mut a = Fq6::rand(&mut rng);
        let mut b = a;

        a.mul_by_01(&c0, &c1);
        b.mul_assign(&Fq6::new(c0, c1, Fq2::zero()));

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq12_mul_by_014() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c1 = Fq2::rand(&mut rng);
        let c5 = Fq2::rand(&mut rng);
        let mut a = Fq12::rand(&mut rng);
        let mut b = a;

        a.mul_by_014(&c0, &c1, &c5);
        b.mul_assign(&Fq12::new(
            Fq6::new(c0, c1, Fq2::zero()),
            Fq6::new(Fq2::zero(), c5, Fq2::zero()),
        ));

        assert_eq!(a, b);
    }
}

#[test]
fn test_fq12_mul_by_034() {
    let mut rng = test_rng();

    for _ in 0..1000 {
        let c0 = Fq2::rand(&mut rng);
        let c3 = Fq2::rand(&mut rng);
        let c4 = Fq2::rand(&mut rng);
        let mut a = Fq12::rand(&mut rng);
        let mut b = a;

        a.mul_by_034(&c0, &c3, &c4);
        b.mul_assign(&Fq12::new(
            Fq6::new(c0, Fq2::zero(), Fq2::zero()),
            Fq6::new(c3, c4, Fq2::zero()),
        ));

        assert_eq!(a, b);
    }
}
