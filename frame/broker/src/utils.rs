use sp_arithmetic::traits::Bounded;

pub fn lerp<T: TryInto<u128>, S: TryInto<u128> + TryFrom<u128> + Bounded>(
	v: T,
	a: T,
	d: T,
	x: S,
	y: S,
) -> Option<S> {
	use sp_arithmetic::{
		helpers_128bit::multiply_by_rational_with_rounding, Rounding::NearestPrefUp,
	};
	let v: u128 = v.try_into().ok()?;
	let a: u128 = a.try_into().ok()?;
	let d: u128 = d.try_into().ok()?;
	let r: u128 = x.try_into().ok()?;
	let s: u128 = y.try_into().ok()?;
	let rsd = r.max(s) - r.min(s);
	let td = multiply_by_rational_with_rounding(rsd, (v.max(a) - a).min(d), d, NearestPrefUp)?;
	if r < s { r + td } else { r - td }.try_into().ok()
}
