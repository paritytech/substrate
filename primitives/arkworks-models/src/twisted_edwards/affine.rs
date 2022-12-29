use ark_serialize::{
	CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError, Valid, Validate,
};
use ark_std::{
	borrow::Borrow,
	fmt::{Debug, Display, Formatter, Result as FmtResult},
	io::{Read, Write},
	ops::{Add, Mul, Neg, Sub},
	rand::{
		distributions::{Distribution, Standard},
		Rng,
	},
	vec::Vec,
};
use derivative::Derivative;
use num_traits::{One, Zero};
use zeroize::Zeroize;

use ark_ff::{fields::Field, PrimeField, ToConstraintField, UniformRand};

use super::{Projective, TECurveConfig, TEFlags};
use crate::AffineRepr;

/// Affine coordinates for a point on a twisted Edwards curve, over the
/// base field `P::BaseField`.
#[derive(Derivative)]
#[derivative(
	Copy(bound = "P: TECurveConfig"),
	Clone(bound = "P: TECurveConfig"),
	PartialEq(bound = "P: TECurveConfig"),
	Eq(bound = "P: TECurveConfig"),
	Hash(bound = "P: TECurveConfig")
)]
#[must_use]
pub struct Affine<P: TECurveConfig> {
	/// X coordinate of the point represented as a field element
	pub x: P::BaseField,
	/// Y coordinate of the point represented as a field element
	pub y: P::BaseField,
}

impl<P: TECurveConfig> Display for Affine<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		match self.is_zero() {
			true => write!(f, "infinity"),
			false => write!(f, "({}, {})", self.x, self.y),
		}
	}
}

impl<P: TECurveConfig> Debug for Affine<P> {
	fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
		match self.is_zero() {
			true => write!(f, "infinity"),
			false => write!(f, "({}, {})", self.x, self.y),
		}
	}
}

impl<P: TECurveConfig> PartialEq<Projective<P>> for Affine<P> {
	fn eq(&self, other: &Projective<P>) -> bool {
		self.into_group() == *other
	}
}

impl<P: TECurveConfig> Affine<P> {
	/// Construct a new group element without checking whether the coordinates
	/// specify a point in the subgroup.
	pub const fn new_unchecked(x: P::BaseField, y: P::BaseField) -> Self {
		Self { x, y }
	}

	/// Construct a new group element in a way while enforcing that points are in
	/// the prime-order subgroup.
	pub fn new(x: P::BaseField, y: P::BaseField) -> Self {
		let p = Self::new_unchecked(x, y);
		assert!(p.is_on_curve());
		assert!(p.is_in_correct_subgroup_assuming_on_curve());
		p
	}

	/// Construct the identity of the group
	pub const fn zero() -> Self {
		Self::new_unchecked(P::BaseField::ZERO, P::BaseField::ONE)
	}

	/// Is this point the identity?
	pub fn is_zero(&self) -> bool {
		self.x.is_zero() && self.y.is_one()
	}

	/// Attempts to construct an affine point given an y-coordinate. The
	/// point is not guaranteed to be in the prime order subgroup.
	///
	/// If and only if `greatest` is set will the lexicographically
	/// largest x-coordinate be selected.
	///
	/// a * X^2 + Y^2 = 1 + d * X^2 * Y^2
	/// a * X^2 - d * X^2 * Y^2 = 1 - Y^2
	/// X^2 * (a - d * Y^2) = 1 - Y^2
	/// X^2 = (1 - Y^2) / (a - d * Y^2)
	#[allow(dead_code)]
	pub fn get_point_from_y_unchecked(y: P::BaseField, greatest: bool) -> Option<Self> {
		Self::get_xs_from_y_unchecked(y).map(|(x, neg_x)| {
			if greatest {
				Self::new_unchecked(neg_x, y)
			} else {
				Self::new_unchecked(x, y)
			}
		})
	}

	/// Attempts to recover the x-coordinate given an y-coordinate. The
	/// resulting point is not guaranteed to be in the prime order subgroup.
	///
	/// If and only if `greatest` is set will the lexicographically
	/// largest x-coordinate be selected.
	///
	/// a * X^2 + Y^2 = 1 + d * X^2 * Y^2
	/// a * X^2 - d * X^2 * Y^2 = 1 - Y^2
	/// X^2 * (a - d * Y^2) = 1 - Y^2
	/// X^2 = (1 - Y^2) / (a - d * Y^2)
	#[allow(dead_code)]
	pub fn get_xs_from_y_unchecked(y: P::BaseField) -> Option<(P::BaseField, P::BaseField)> {
		let y2 = y.square();

		let numerator = P::BaseField::one() - y2;
		let denominator = P::COEFF_A - (y2 * P::COEFF_D);

		denominator
			.inverse()
			.map(|denom| denom * &numerator)
			.and_then(|x2| x2.sqrt())
			.map(|x| {
				let neg_x = -x;
				if x <= neg_x {
					(x, neg_x)
				} else {
					(neg_x, x)
				}
			})
	}

	/// Checks that the current point is on the elliptic curve.
	pub fn is_on_curve(&self) -> bool {
		let x2 = self.x.square();
		let y2 = self.y.square();

		let lhs = y2 + P::mul_by_a(x2);
		let rhs = P::BaseField::one() + &(P::COEFF_D * &(x2 * &y2));

		lhs == rhs
	}
}

impl<P: TECurveConfig> Affine<P> {
	/// Checks if `self` is in the subgroup having order equaling that of
	/// `P::ScalarField` given it is on the curve.
	pub fn is_in_correct_subgroup_assuming_on_curve(&self) -> bool {
		P::is_in_correct_subgroup_assuming_on_curve(self)
	}
}

impl<P: TECurveConfig> AffineRepr for Affine<P> {
	type Config = P;
	type BaseField = P::BaseField;
	type ScalarField = P::ScalarField;
	type Group = Projective<P>;

	fn xy(&self) -> Option<(&Self::BaseField, &Self::BaseField)> {
		(!self.is_zero()).then(|| (&self.x, &self.y))
	}

	fn generator() -> Self {
		P::GENERATOR
	}

	fn zero() -> Self {
		Self::new_unchecked(P::BaseField::ZERO, P::BaseField::ONE)
	}

	fn from_random_bytes(bytes: &[u8]) -> Option<Self> {
		P::BaseField::from_random_bytes_with_flags::<TEFlags>(bytes)
			.and_then(|(y, flags)| Self::get_point_from_y_unchecked(y, flags.is_negative()))
	}

	fn mul_bigint(&self, by: impl AsRef<[u64]>) -> Self::Group {
		P::mul_affine(self, by.as_ref())
	}

	/// Multiplies this element by the cofactor and output the
	/// resulting projective element.
	#[must_use]
	fn mul_by_cofactor_to_group(&self) -> Self::Group {
		P::mul_affine(self, Self::Config::COFACTOR)
	}

	/// Performs cofactor clearing.
	/// The default method is simply to multiply by the cofactor.
	/// Some curves can implement a more efficient algorithm.
	fn clear_cofactor(&self) -> Self {
		P::clear_cofactor(self)
	}
}

impl<P: TECurveConfig> Zeroize for Affine<P> {
	// The phantom data does not contain element-specific data
	// and thus does not need to be zeroized.
	fn zeroize(&mut self) {
		self.x.zeroize();
		self.y.zeroize();
	}
}

impl<P: TECurveConfig> Neg for Affine<P> {
	type Output = Self;

	fn neg(self) -> Self {
		Self::new_unchecked(-self.x, self.y)
	}
}

impl<P: TECurveConfig, T: Borrow<Self>> Add<T> for Affine<P> {
	type Output = Projective<P>;
	fn add(self, other: T) -> Self::Output {
		let mut copy = self.into_group();
		copy += other.borrow();
		copy
	}
}

impl<P: TECurveConfig> Add<Projective<P>> for Affine<P> {
	type Output = Projective<P>;
	fn add(self, other: Projective<P>) -> Projective<P> {
		other + self
	}
}

impl<'a, P: TECurveConfig> Add<&'a Projective<P>> for Affine<P> {
	type Output = Projective<P>;
	fn add(self, other: &'a Projective<P>) -> Projective<P> {
		*other + self
	}
}

impl<P: TECurveConfig, T: Borrow<Self>> Sub<T> for Affine<P> {
	type Output = Projective<P>;
	fn sub(self, other: T) -> Self::Output {
		let mut copy = self.into_group();
		copy -= other.borrow();
		copy
	}
}

impl<P: TECurveConfig> Default for Affine<P> {
	#[inline]
	fn default() -> Self {
		Self::zero()
	}
}

impl<P: TECurveConfig> Distribution<Affine<P>> for Standard {
	/// Generates a uniformly random instance of the curve.
	#[inline]
	fn sample<R: Rng + ?Sized>(&self, rng: &mut R) -> Affine<P> {
		loop {
			let y = P::BaseField::rand(rng);
			let greatest = rng.gen();

			if let Some(p) = Affine::get_point_from_y_unchecked(y, greatest) {
				return p.mul_by_cofactor()
			}
		}
	}
}

impl<P: TECurveConfig, T: Borrow<P::ScalarField>> Mul<T> for Affine<P> {
	type Output = Projective<P>;

	#[inline]
	fn mul(self, other: T) -> Self::Output {
		self.mul_bigint(other.borrow().into_bigint())
	}
}

// The projective point X, Y, T, Z is represented in the affine
// coordinates as X/Z, Y/Z.
impl<P: TECurveConfig> From<Projective<P>> for Affine<P> {
	fn from(p: Projective<P>) -> Affine<P> {
		if p.is_zero() {
			Affine::zero()
		} else if p.z.is_one() {
			// If Z is one, the point is already normalized.
			Affine::new_unchecked(p.x, p.y)
		} else {
			// Z is nonzero, so it must have an inverse in a field.
			let z_inv = p.z.inverse().unwrap();
			let x = p.x * &z_inv;
			let y = p.y * &z_inv;
			Affine::new_unchecked(x, y)
		}
	}
}
impl<P: TECurveConfig> CanonicalSerialize for Affine<P> {
	#[inline]
	fn serialize_with_mode<W: Write>(
		&self,
		writer: W,
		compress: ark_serialize::Compress,
	) -> Result<(), SerializationError> {
		P::serialize_with_mode(self, writer, compress)
	}

	#[inline]
	fn serialized_size(&self, compress: Compress) -> usize {
		P::serialized_size(compress)
	}
}

impl<P: TECurveConfig> Valid for Affine<P> {
	fn check(&self) -> Result<(), SerializationError> {
		if self.is_on_curve() && self.is_in_correct_subgroup_assuming_on_curve() {
			Ok(())
		} else {
			Err(SerializationError::InvalidData)
		}
	}
}

impl<P: TECurveConfig> CanonicalDeserialize for Affine<P> {
	fn deserialize_with_mode<R: Read>(
		reader: R,
		compress: Compress,
		validate: Validate,
	) -> Result<Self, SerializationError> {
		P::deserialize_with_mode(reader, compress, validate)
	}
}

impl<M: TECurveConfig, ConstraintF: Field> ToConstraintField<ConstraintF> for Affine<M>
where
	M::BaseField: ToConstraintField<ConstraintF>,
{
	#[inline]
	fn to_field_elements(&self) -> Option<Vec<ConstraintF>> {
		let mut x_fe = self.x.to_field_elements()?;
		let y_fe = self.y.to_field_elements()?;
		x_fe.extend_from_slice(&y_fe);
		Some(x_fe)
	}
}
