use ark_serialize::{
	CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
	borrow::Borrow,
	fmt::{Display, Formatter, Result as FmtResult},
	hash::{Hash, Hasher},
	io::{Read, Write},
	ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
	rand::{
		distributions::{Distribution, Standard},
		Rng,
	},
	vec::Vec,
	One, Zero,
};
use derivative::Derivative;

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

use zeroize::Zeroize;

#[cfg(feature = "parallel")]
use rayon::prelude::*;

use super::{Affine, MontCurveConfig, TECurveConfig};
use crate::{
	scalar_mul::{variable_base::VariableBaseMSM, ScalarMul},
	AffineRepr, CurveGroup, Group,
};

/// `Projective` implements Extended Twisted Edwards Coordinates
/// as described in [\[HKCD08\]](https://eprint.iacr.org/2008/522.pdf).
///
/// This implementation uses the unified addition formulae from that paper (see
/// Section 3.1).
#[derive(Derivative)]
#[derivative(
	Copy(bound = "P: TECurveConfig"),
	Clone(bound = "P: TECurveConfig"),
	Eq(bound = "P: TECurveConfig"),
	Debug(bound = "P: TECurveConfig")
)]
#[must_use]
pub struct Projective<P: TECurveConfig> {
	pub x: P::BaseField,
	pub y: P::BaseField,
	pub t: P::BaseField,
	pub z: P::BaseField,
}

impl<P: TECurveConfig> PartialEq<Affine<P>> for Projective<P> {
	fn eq(&self, other: &Affine<P>) -> bool {
		*self == other.into_group()
	}
}

impl<P: TECurveConfig> Display for Projective<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		write!(f, "{}", Affine::from(*self))
	}
}

impl<P: TECurveConfig> PartialEq for Projective<P> {
	fn eq(&self, other: &Self) -> bool {
		if self.is_zero() {
			return other.is_zero()
		}

		if other.is_zero() {
			return false
		}

		// x1/z1 == x2/z2  <==> x1 * z2 == x2 * z1
		(self.x * &other.z) == (other.x * &self.z) && (self.y * &other.z) == (other.y * &self.z)
	}
}

impl<P: TECurveConfig> Hash for Projective<P> {
	fn hash<H: Hasher>(&self, state: &mut H) {
		self.into_affine().hash(state)
	}
}

impl<P: TECurveConfig> Distribution<Projective<P>> for Standard {
	/// Generates a uniformly random instance of the curve.
	#[inline]
	fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Projective<P> {
		loop {
			let y = P::BaseField::rand(rng);
			let greatest = rng.gen();

			if let Some(p) = Affine::get_point_from_y_unchecked(y, greatest) {
				return p.mul_by_cofactor_to_group()
			}
		}
	}
}

impl<P: TECurveConfig> Default for Projective<P> {
	#[inline]
	fn default() -> Self {
		Self::zero()
	}
}

impl<P: TECurveConfig> Projective<P> {
	/// Construct a new group element without checking whether the coordinates
	/// specify a point in the subgroup.
	pub const fn new_unchecked(
		x: P::BaseField,
		y: P::BaseField,
		t: P::BaseField,
		z: P::BaseField,
	) -> Self {
		Self { x, y, t, z }
	}

	/// Construct a new group element in a way while enforcing that points are in
	/// the prime-order subgroup.
	pub fn new(x: P::BaseField, y: P::BaseField, t: P::BaseField, z: P::BaseField) -> Self {
		let p = Self::new_unchecked(x, y, t, z).into_affine();
		assert!(p.is_on_curve());
		assert!(p.is_in_correct_subgroup_assuming_on_curve());
		p.into()
	}
}
impl<P: TECurveConfig> Zeroize for Projective<P> {
	// The phantom data does not contain element-specific data
	// and thus does not need to be zeroized.
	fn zeroize(&mut self) {
		self.x.zeroize();
		self.y.zeroize();
		self.t.zeroize();
		self.z.zeroize();
	}
}

impl<P: TECurveConfig> Zero for Projective<P> {
	fn zero() -> Self {
		Self::new_unchecked(
			P::BaseField::zero(),
			P::BaseField::one(),
			P::BaseField::zero(),
			P::BaseField::one(),
		)
	}

	fn is_zero(&self) -> bool {
		self.x.is_zero() && self.y == self.z && !self.y.is_zero() && self.t.is_zero()
	}
}

impl<P: TECurveConfig> Group for Projective<P> {
	type ScalarField = P::ScalarField;

	fn generator() -> Self {
		Affine::generator().into()
	}

	fn double_in_place(&mut self) -> &mut Self {
		// See "Twisted Edwards Curves Revisited"
		// Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
		// 3.3 Doubling in E^e
		// Source: https://www.hyperelliptic.org/EFD/g1p/data/twisted/extended/doubling/dbl-2008-hwcd

		// A = X1^2
		let a = self.x.square();
		// B = Y1^2
		let b = self.y.square();
		// C = 2 * Z1^2
		let c = self.z.square().double();
		// D = a * A
		let d = P::mul_by_a(a);
		// E = (X1 + Y1)^2 - A - B
		let e = (self.x + &self.y).square() - &a - &b;
		// G = D + B
		let g = d + &b;
		// F = G - C
		let f = g - &c;
		// H = D - B
		let h = d - &b;
		// X3 = E * F
		self.x = e * &f;
		// Y3 = G * H
		self.y = g * &h;
		// T3 = E * H
		self.t = e * &h;
		// Z3 = F * G
		self.z = f * &g;

		self
	}

	#[inline]
	fn mul_bigint(&self, other: impl AsRef<[u64]>) -> Self {
		P::mul_projective(self, other.as_ref())
	}
}

impl<P: TECurveConfig> CurveGroup for Projective<P> {
	type Config = P;
	type BaseField = P::BaseField;
	type Affine = Affine<P>;
	type FullGroup = Affine<P>;

	fn normalize_batch(v: &[Self]) -> Vec<Self::Affine> {
		// A projective curve element (x, y, t, z) is normalized
		// to its affine representation, by the conversion
		// (x, y, t, z) -> (x/z, y/z, t/z, 1)
		// Batch normalizing N twisted edwards curve elements costs:
		//     1 inversion + 6N field multiplications
		// (batch inversion requires 3N multiplications + 1 inversion)
		let mut z_s = v.iter().map(|g| g.z).collect::<Vec<_>>();
		ark_ff::batch_inversion(&mut z_s);

		// Perform affine transformations
		ark_std::cfg_iter!(v)
			.zip(z_s)
			.map(|(g, z)| match g.is_zero() {
				true => Affine::zero(),
				false => {
					let x = g.x * &z;
					let y = g.y * &z;
					Affine::new_unchecked(x, y)
				},
			})
			.collect()
	}
}

impl<P: TECurveConfig> Neg for Projective<P> {
	type Output = Self;
	fn neg(mut self) -> Self {
		self.x = -self.x;
		self.t = -self.t;
		self
	}
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> AddAssign<T> for Projective<P> {
	fn add_assign(&mut self, other: T) {
		let other = other.borrow();
		// See "Twisted Edwards Curves Revisited"
		// Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
		// 3.1 Unified Addition in E^e
		// Source: https://www.hyperelliptic.org/EFD/g1p/data/twisted/extended/addition/madd-2008-hwcd

		// A = X1*X2
		let a = self.x * &other.x;
		// B = Y1*Y2
		let b = self.y * &other.y;
		// C = T1*d*T2
		let c = P::COEFF_D * &self.t * &other.x * &other.y;

		// D = Z1
		let d = self.z;
		// E = (X1+Y1)*(X2+Y2)-A-B
		let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;
		// F = D-C
		let f = d - &c;
		// G = D+C
		let g = d + &c;
		// H = B-a*A
		let h = b - &P::mul_by_a(a);
		// X3 = E*F
		self.x = e * &f;
		// Y3 = G*H
		self.y = g * &h;
		// T3 = E*H
		self.t = e * &h;
		// Z3 = F*G
		self.z = f * &g;
	}
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> Add<T> for Projective<P> {
	type Output = Self;
	fn add(mut self, other: T) -> Self {
		let other = other.borrow();
		self += other;
		self
	}
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> SubAssign<T> for Projective<P> {
	fn sub_assign(&mut self, other: T) {
		*self += -(*other.borrow());
	}
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> Sub<T> for Projective<P> {
	type Output = Self;
	fn sub(mut self, other: T) -> Self {
		self -= other.borrow();
		self
	}
}
ark_ff::impl_additive_ops_from_ref!(Projective, TECurveConfig);

impl<'a, P: TECurveConfig> Add<&'a Self> for Projective<P> {
	type Output = Self;
	fn add(mut self, other: &'a Self) -> Self {
		self += other;
		self
	}
}

impl<'a, P: TECurveConfig> Sub<&'a Self> for Projective<P> {
	type Output = Self;
	fn sub(mut self, other: &'a Self) -> Self {
		self -= other;
		self
	}
}

impl<'a, P: TECurveConfig> AddAssign<&'a Self> for Projective<P> {
	fn add_assign(&mut self, other: &'a Self) {
		// See "Twisted Edwards Curves Revisited" (https://eprint.iacr.org/2008/522.pdf)
		// by Huseyin Hisil, Kenneth Koon-Ho Wong, Gary Carter, and Ed Dawson
		// 3.1 Unified Addition in E^e

		// A = x1 * x2
		let a = self.x * &other.x;

		// B = y1 * y2
		let b = self.y * &other.y;

		// C = d * t1 * t2
		let c = P::COEFF_D * &self.t * &other.t;

		// D = z1 * z2
		let d = self.z * &other.z;

		// H = B - aA
		let h = b - &P::mul_by_a(a);

		// E = (x1 + y1) * (x2 + y2) - A - B
		let e = (self.x + &self.y) * &(other.x + &other.y) - &a - &b;

		// F = D - C
		let f = d - &c;

		// G = D + C
		let g = d + &c;

		// x3 = E * F
		self.x = e * &f;

		// y3 = G * H
		self.y = g * &h;

		// t3 = E * H
		self.t = e * &h;

		// z3 = F * G
		self.z = f * &g;
	}
}

impl<'a, P: TECurveConfig> SubAssign<&'a Self> for Projective<P> {
	fn sub_assign(&mut self, other: &'a Self) {
		*self += -(*other);
	}
}

impl<P: TECurveConfig, T: Borrow<P::ScalarField>> MulAssign<T> for Projective<P> {
	fn mul_assign(&mut self, other: T) {
		*self = self.mul_bigint(other.borrow().into_bigint())
	}
}

impl<P: TECurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Projective<P> {
	type Output = Self;

	#[inline]
	fn mul(mut self, other: T) -> Self {
		self *= other;
		self
	}
}

impl<P: TECurveConfig, T: Borrow<Affine<P>>> ark_std::iter::Sum<T> for Projective<P> {
	fn sum<I>(iter: I) -> Self
	where
		I: Iterator<Item = T>,
	{
		iter.fold(Self::zero(), |acc, x| acc + x.borrow())
	}
}

// The affine point (X, Y) is represented in the Extended Projective coordinates
// with Z = 1.
impl<P: TECurveConfig> From<Affine<P>> for Projective<P> {
	fn from(p: Affine<P>) -> Projective<P> {
		Self::new_unchecked(p.x, p.y, p.x * &p.y, P::BaseField::one())
	}
}

#[derive(Derivative)]
#[derivative(
	Copy(bound = "P: MontCurveConfig"),
	Clone(bound = "P: MontCurveConfig"),
	PartialEq(bound = "P: MontCurveConfig"),
	Eq(bound = "P: MontCurveConfig"),
	Debug(bound = "P: MontCurveConfig"),
	Hash(bound = "P: MontCurveConfig")
)]
pub struct MontgomeryAffine<P: MontCurveConfig> {
	pub x: P::BaseField,
	pub y: P::BaseField,
}

impl<P: MontCurveConfig> Display for MontgomeryAffine<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		write!(f, "MontgomeryAffine(x={}, y={})", self.x, self.y)
	}
}

impl<P: MontCurveConfig> MontgomeryAffine<P> {
	pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
		Self { x, y }
	}
}

impl<P: TECurveConfig> CanonicalSerialize for Projective<P> {
	#[allow(unused_qualifications)]
	#[inline]
	fn serialize_with_mode<W: Write>(
		&self,
		writer: W,
		compress: Compress,
	) -> Result<(), SerializationError> {
		let aff = Affine::<P>::from(*self);
		P::serialize_with_mode(&aff, writer, compress)
	}

	#[inline]
	fn serialized_size(&self, compress: Compress) -> usize {
		P::serialized_size(compress)
	}
}

impl<P: TECurveConfig> Valid for Projective<P> {
	fn check(&self) -> Result<(), SerializationError> {
		self.into_affine().check()
	}

	fn batch_check<'a>(
		batch: impl Iterator<Item = &'a Self> + Send,
	) -> Result<(), SerializationError>
	where
		Self: 'a,
	{
		let batch = batch.copied().collect::<Vec<_>>();
		let batch = Self::normalize_batch(&batch);
		Affine::batch_check(batch.iter())
	}
}

impl<P: TECurveConfig> CanonicalDeserialize for Projective<P> {
	#[allow(unused_qualifications)]
	fn deserialize_with_mode<R: Read>(
		reader: R,
		compress: Compress,
		validate: Validate,
	) -> Result<Self, SerializationError> {
		let aff = P::deserialize_with_mode(reader, compress, validate)?;
		Ok(aff.into())
	}
}

impl<M: TECurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Projective<M>
where
	M::BaseField: ToConstraintField<ConstraintF>,
{
	#[inline]
	fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
		Affine::from(*self).to_field_elements()
	}
}

impl<P: TECurveConfig> ScalarMul for Projective<P> {
	type MulBase = Affine<P>;
	const NEGATION_IS_CHEAP: bool = true;

	fn batch_convert_to_mul_base(bases: &[Self]) -> Vec<Self::MulBase> {
		Self::normalize_batch(bases)
	}
}

impl<P: TECurveConfig> VariableBaseMSM for Projective<P> {
	fn msm(bases: &[Self::MulBase], bigints: &[Self::ScalarField]) -> Result<Self, usize> {
		P::msm(bases, bigints)
	}
}
