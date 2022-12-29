use ark_serialize::{
	CanonicalDeserialize, CanonicalDeserializeWithFlags, CanonicalSerialize,
	CanonicalSerializeWithFlags, Compress, SerializationError, Valid, Validate,
};
use ark_std::io::{Read, Write};

use crate::{scalar_mul::variable_base::VariableBaseMSM, AffineRepr, Group};
use num_traits::Zero;

use ark_ff::fields::Field;

mod affine;
pub use affine::*;

mod group;
pub use group::*;

mod serialization_flags;
pub use serialization_flags::*;

/// Constants and convenience functions that collectively define the [Twisted Edwards model](https://www.hyperelliptic.org/EFD/g1p/auto-twisted.html)
/// of the curve. In this model, the curve equation is
/// `a * x² + y² = 1 + d * x² * y²`, for constants `a` and `d`.
pub trait TECurveConfig: super::CurveConfig {
	/// Coefficient `a` of the curve equation.
	const COEFF_A: Self::BaseField;
	/// Coefficient `d` of the curve equation.
	const COEFF_D: Self::BaseField;
	/// Generator of the prime-order subgroup.
	const GENERATOR: Affine<Self>;

	/// Model parameters for the Montgomery curve that is birationally
	/// equivalent to this curve.
	type MontCurveConfig: MontCurveConfig<BaseField = Self::BaseField>;

	/// Helper method for computing `elem * Self::COEFF_A`.
	///
	/// The default implementation should be overridden only if
	/// the product can be computed faster than standard field multiplication
	/// (eg: via doubling if `COEFF_A == 2`, or if `COEFF_A.is_zero()`).
	#[inline(always)]
	fn mul_by_a(elem: Self::BaseField) -> Self::BaseField {
		elem * Self::COEFF_A
	}

	/// Checks that the current point is in the prime order subgroup given
	/// the point on the curve.
	fn is_in_correct_subgroup_assuming_on_curve(item: &Affine<Self>) -> bool {
		Self::mul_affine(item, Self::ScalarField::characteristic()).is_zero()
	}

	/// Performs cofactor clearing.
	/// The default method is simply to multiply by the cofactor.
	/// For some curve families though, it is sufficient to multiply
	/// by a smaller scalar.
	fn clear_cofactor(item: &Affine<Self>) -> Affine<Self> {
		item.mul_by_cofactor()
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
	/// coordinates
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

	/// If uncompressed, serializes both x and y coordinates.
	/// If compressed, serializes y coordinate with a bit to encode whether x is positive.
	#[inline]
	fn serialize_with_mode<W: Write>(
		item: &Affine<Self>,
		mut writer: W,
		compress: ark_serialize::Compress,
	) -> Result<(), SerializationError> {
		let flags = TEFlags::from_x_coordinate(item.x);
		match compress {
			Compress::Yes => item.y.serialize_with_flags(writer, flags),
			Compress::No => {
				item.x.serialize_uncompressed(&mut writer)?;
				item.y.serialize_uncompressed(&mut writer)
			},
		}
	}

	/// If `validate` is `Yes`, calls `check()` to make sure the element is valid.
	///
	/// Uses `Affine::get_xs_from_y_unchecked()` for the compressed version.
	fn deserialize_with_mode<R: Read>(
		mut reader: R,
		compress: Compress,
		validate: Validate,
	) -> Result<Affine<Self>, SerializationError> {
		let (x, y) = match compress {
			Compress::Yes => {
				let (y, flags): (_, TEFlags) =
					CanonicalDeserializeWithFlags::deserialize_with_flags(reader)?;
				let (x, neg_x) = Affine::<Self>::get_xs_from_y_unchecked(y)
					.ok_or(SerializationError::InvalidData)?;
				if flags.is_negative() {
					(neg_x, y)
				} else {
					(x, y)
				}
			},
			Compress::No => {
				let x: Self::BaseField =
					CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
				let y: Self::BaseField =
					CanonicalDeserialize::deserialize_uncompressed(&mut reader)?;
				(x, y)
			},
		};
		let point = Affine::<Self>::new_unchecked(x, y);
		if let Validate::Yes = validate {
			point.check()?;
		}
		Ok(point)
	}

	#[inline]
	fn serialized_size(compress: Compress) -> usize {
		let zero = Self::BaseField::zero();
		match compress {
			Compress::Yes => zero.serialized_size_with_flags::<TEFlags>(),
			Compress::No => zero.uncompressed_size() + zero.uncompressed_size(),
		}
	}
}

/// Constants and convenience functions that collectively define the [Montgomery model](https://www.hyperelliptic.org/EFD/g1p/auto-montgom.html)
/// of the curve. In this model, the curve equation is
/// `b * y² = x³ + a * x² + x`, for constants `a` and `b`.
pub trait MontCurveConfig: super::CurveConfig {
	/// Coefficient `a` of the curve equation.
	const COEFF_A: Self::BaseField;
	/// Coefficient `b` of the curve equation.
	const COEFF_B: Self::BaseField;

	/// Model parameters for the Twisted Edwards curve that is birationally
	/// equivalent to this curve.
	type TECurveConfig: TECurveConfig<BaseField = Self::BaseField>;
}

//////////////////////////////////////////////////////////////////////////////
