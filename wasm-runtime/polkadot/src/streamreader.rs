use slicable::Slicable;

pub struct StreamReader<'a> {
	data: &'a[u8],
	offset: usize,
}

impl<'a> StreamReader<'a> {
	pub fn new(data: &'a[u8]) -> Self {
		StreamReader {
			data: data,
			offset: 0,
		}
	}
	pub fn read<T: Slicable>(&mut self) -> Option<T> {
		let size = T::size_of(&self.data[self.offset..])?;
		let new_offset = self.offset + size;
		let slice = &self.data[self.offset..new_offset];
		self.offset = new_offset;
		Slicable::from_slice(slice)
	}
}
/*
// Not in use yet
// TODO: introduce fn size_will_be(&self) -> usize; to Slicable trait and implement
struct StreamWriter<'a> {
	data: &'a mut[u8],
	offset: usize,
}

impl<'a> StreamWriter<'a> {
	pub fn new(data: &'a mut[u8]) -> Self {
		StreamWriter {
			data: data,
			offset: 0,
		}
	}
	pub fn write<T: Slicable>(&mut self, value: &T) -> bool {
		value.as_slice_then(|s| {
			let new_offset = self.offset + s.len();
			if self.data.len() <= new_offset {
				let slice = &mut self.data[self.offset..new_offset];
				self.offset = new_offset;
				slice.copy_from_slice(s);
				true
			} else {
				false
			}
		})
	}
}
*/
