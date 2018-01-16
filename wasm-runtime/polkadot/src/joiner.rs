use slicable::Slicable;

pub trait Joiner {
	fn join<T: Slicable + Sized>(self, value: &T) -> Self;
}

impl Joiner for Vec<u8> {
	fn join<T: Slicable + Sized>(mut self, value: &T) -> Vec<u8> {
		value.as_slice_then(|s| self.extend_from_slice(s));
		self
	}
}
