use super::{TypeMetadata, TypeMetadataKind, MetadataName};

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
	>(&mut self, name: MetadataName, f: F) {
		// simple primitive types are ignored to reduce storage usage
		// and they are assumed to be decodable by all valid decoder implementations
		// TODO: only save metadata with custom names. i.e. No need to save Vec<MyStruct> but MyStruct needs to be saved
		let should_ignore = match name {
			MetadataName::Custom(_, _) => false,
			MetadataName::Array(_, _) => false,
			MetadataName::Vector(_) => false,
			MetadataName::Tuple(_) => false,
			MetadataName::Option(_) => false,
			MetadataName::Result(_, _) => false,
			_ => true
		};
		if should_ignore {
			return;
		}
		if self.get(&name).is_some() {
			return;
		}
		let m = TypeMetadata {
			kind: TypeMetadataKind::Primitive,
			name,
		};
		self.list.push(m);
		let idx = self.list.len();
		// needs to be called after self type is registered incase it reference self type again
		self.list[idx - 1].kind = f(self);
	}

	fn get(&self, name: &MetadataName) -> Option<TypeMetadata> {
		self.list.iter().find(|m| m.name == *name).map(|m| m.clone())
	}
}
