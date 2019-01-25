use super::{TypeMetadata, TypeMetadataKind, PrimativeMetadata, StringBuf};

use rstd::prelude::*;

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct MetadataRegistry {
	list: Vec<TypeMetadata>,
}

impl MetadataRegistry {
	pub fn new() -> MetadataRegistry {
		MetadataRegistry {
			list: Vec::new()
		}
	}

	pub fn register<
		F: Fn(& mut MetadataRegistry) -> TypeMetadataKind
	>(&mut self, name: &Vec<StringBuf>, f: F) {
		if self.get(name).is_some() {
			return;
		}
		let m = TypeMetadata {
			kind: TypeMetadataKind::Primative(PrimativeMetadata::Unknown),
			name: name.clone(),
		};
		self.list.push(m);
		let idx = self.list.len();
		// needs to be called after self type is registered incase it reference self type again
		self.list[idx - 1].kind = f(self);
	}

	pub fn get(&self, name: &Vec<StringBuf>) -> Option<TypeMetadata> {
		self.list.iter().find(|m| m.name == *name).map(|m| m.clone())
	}
}
