use std::cmp::PartialOrd;

pub fn value_between<T: PartialOrd>(value: T, min: T, max: T) -> Option<T> {
	if value >= min && value < max {
		Some(value)
	} else {
		None
	}
}
