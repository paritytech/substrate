use super::{TypeMetadata, TypeMetadataKind, StringBuf};

#[derive(Encode, Clone)]
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
			kind: f(self),
			name: name.clone(),
		};
		self.list.push(m);
	}

	pub fn get(&self, name: &Vec<StringBuf>) -> Option<TypeMetadata> {
		self.list.iter().find(|m| m.name == *name).map(|m| m.clone())
	}
}
