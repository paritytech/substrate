#[cfg(feature = "std")]
use serde_derive::Serialize;

#[cfg(feature = "std")]
use parity_codec_derive::Decode;

use parity_codec_derive::Encode;

use super::{TypeMetadata, TypeMetadataKind, MetadataName};

use rstd::prelude::*;

#[derive(Encode, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "std", derive(Decode, Debug, Serialize))]
pub struct MetadataRegistry {
	pub list: Vec<TypeMetadata>,
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
		let should_ignore = match name {
			MetadataName::Custom(_, _) => false,
			MetadataName::CustomWithGenerics(_, _, _) => false,
			MetadataName::Array(_, _) |
			MetadataName::Vector(_) |
			MetadataName::Tuple(_) |
			MetadataName::Option(_) |
			MetadataName::Result(_, _) => {
				// build-ins are also ignored but their sub-types are registered
				f(self);
				true
			}
			_ => true
		};
		if should_ignore {
			return;
		}
		if self.exists(&name) {
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

	fn exists(&self, name: &MetadataName) -> bool {
		self.list.iter().find(|m| m.name == *name).is_some()
	}
}
