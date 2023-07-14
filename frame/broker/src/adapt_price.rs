use crate::CoreIndex;
use sp_arithmetic::{traits::One, FixedU64};

pub trait AdaptPrice {
	fn adapt_price(sold: CoreIndex, target: CoreIndex, max: CoreIndex) -> FixedU64;
}

impl AdaptPrice for () {
	fn adapt_price(_: CoreIndex, _: CoreIndex, _: CoreIndex) -> FixedU64 {
		FixedU64::one()
	}
}

pub struct Linear;
impl AdaptPrice for Linear {
	fn adapt_price(sold: CoreIndex, target: CoreIndex, max: CoreIndex) -> FixedU64 {
		if sold < target {
			FixedU64::from_rational(sold.into(), target.into())
		} else {
			FixedU64::one() + FixedU64::from_rational((sold - target).into(), (max - target).into())
		}
	}
}
