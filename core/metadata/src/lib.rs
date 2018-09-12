// Copyright 2017 Parity Technologies (UK) Ltd.
// This file is part of Substrate.

// Substrate is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// Substrate is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with Substrate.  If not, see <http://www.gnu.org/licenses/>.

//! Decodable variant of the JsonMetadata.
//!
//! This really doesn't belong here, but is necessary for the moment. In the future
//! it should be removed entirely to an external module for shimming on to the
//! codec-encoded metadata.

#![cfg_attr(not(feature = "std"), no_std)]

extern crate parity_codec as codec;

use codec::{Encode, Output};
#[cfg(feature = "std")]
use codec::{Decode, Input};

/// The metadata of a runtime encoded as JSON.
#[derive(Eq)]
#[cfg_attr(feature = "std", derive(Debug))]
pub enum JsonMetadata {
	Events { name: &'static str, events: &'static [(&'static str, fn() -> &'static str)] },
	Module { module: &'static str, prefix: &'static str },
	ModuleWithStorage { module: &'static str, prefix: &'static str, storage: &'static str }
}

impl Encode for JsonMetadata {
	fn encode_to<W: Output>(&self, dest: &mut W) {
		match self {
			JsonMetadata::Events { name, events } => {
				0i8.encode_to(dest);
				name.encode_to(dest);
				events.iter().fold(0u32, |count, _| count + 1).encode_to(dest);
				events
					.iter()
					.map(|(module, data)| (module, data()))
					.for_each(|val| val.encode_to(dest));
			},
			JsonMetadata::Module { module, prefix } => {
				1i8.encode_to(dest);
				prefix.encode_to(dest);
				module.encode_to(dest);
			},
			JsonMetadata::ModuleWithStorage { module, prefix, storage } => {
				2i8.encode_to(dest);
				prefix.encode_to(dest);
				module.encode_to(dest);
				storage.encode_to(dest);
			}
		}
	}
}

impl PartialEq<JsonMetadata> for JsonMetadata {
	fn eq(&self, other: &JsonMetadata) -> bool {
		match (self, other) {
			(
				JsonMetadata::Events { name: lname, events: left },
				JsonMetadata::Events { name: rname, events: right }
			) => {
				lname == rname && left.iter().zip(right.iter()).fold(true, |res, (l, r)| {
					res && l.0 == r.0 && l.1() == r.1()
				})
			},
			(
				JsonMetadata::Module { prefix: lpre, module: lmod },
				JsonMetadata::Module { prefix: rpre, module: rmod }
			) => {
				lpre == rpre && lmod == rmod
			},
			(
				JsonMetadata::ModuleWithStorage { prefix: lpre, module: lmod, storage: lstore },
				JsonMetadata::ModuleWithStorage { prefix: rpre, module: rmod, storage: rstore }
			) => {
				lpre == rpre && lmod == rmod && lstore == rstore
			},
			_ => false,
		}
    }
}

/// Utility struct for making `JsonMetadata` decodeable.
#[derive(Eq, PartialEq, Debug)]
#[cfg(feature = "std")]
pub enum JsonMetadataDecodable {
	Events { name: String, events: Vec<(String, String)> },
	Module { module: String, prefix: String },
	ModuleWithStorage { module: String, prefix: String, storage: String }
}

#[cfg(feature = "std")]
impl JsonMetadataDecodable {
	/// Returns the instance as JSON string.
	/// The first value of the tuple is the name of the metadata type and the second in the JSON string.
	pub fn into_json_string(self) -> (&'static str, String) {
		match self {
			JsonMetadataDecodable::Events { name, events } => {
				(
					"events",
					format!(
						r#"{{ "name": "{}", "events": {{ {} }} }}"#, name,
						events.iter().enumerate()
							.fold(String::from(""), |mut json, (i, (name, data))| {
								if i > 0 {
									json.push_str(", ");
								}
								json.push_str(&format!(r#""{}": {}"#, name, data));
								json
							})
					)
				)
			},
			JsonMetadataDecodable::Module { prefix, module } => {
				("module", format!(r#"{{ "prefix": "{}", "module": {} }}"#, prefix, module))
			},
			JsonMetadataDecodable::ModuleWithStorage { prefix, module, storage } => {
				(
					"moduleWithStorage",
					format!(
						r#"{{ "prefix": "{}", "module": {}, "storage": {} }}"#,
						prefix, module, storage
					)
				)
			}
		}
	}
}

#[cfg(feature = "std")]
impl Decode for JsonMetadataDecodable {
	fn decode<I: Input>(input: &mut I) -> Option<Self> {
		i8::decode(input).and_then(|variant| {
			match variant {
				0 => String::decode(input)
						.and_then(|name| Vec::<(String, String)>::decode(input).map(|events| (name, events)))
						.and_then(|(name, events)| Some(JsonMetadataDecodable::Events { name, events })),
				1 => String::decode(input)
						.and_then(|prefix| String::decode(input).map(|v| (prefix, v)))
						.and_then(|(prefix, module)| Some(JsonMetadataDecodable::Module { prefix, module })),
				2 => String::decode(input)
						.and_then(|prefix| String::decode(input).map(|v| (prefix, v)))
						.and_then(|(prefix, module)| String::decode(input).map(|v| (prefix, module, v)))
						.and_then(|(prefix, module, storage)| Some(JsonMetadataDecodable::ModuleWithStorage { prefix, module, storage })),
				_ => None,
			}
		})
	}
}

#[cfg(feature = "std")]
impl PartialEq<JsonMetadata> for JsonMetadataDecodable {
	fn eq(&self, other: &JsonMetadata) -> bool {
		match (self, other) {
			(
				JsonMetadataDecodable::Events { name: lname, events: left },
				JsonMetadata::Events { name: rname, events: right }
			) => {
				lname == rname && left.iter().zip(right.iter()).fold(true, |res, (l, r)| {
					res && l.0 == r.0 && l.1 == r.1()
				})
			},
			(
				JsonMetadataDecodable::Module { prefix: lpre, module: lmod },
				JsonMetadata::Module { prefix: rpre, module: rmod }
			) => {
				lpre == rpre && lmod == rmod
			},
			(
				JsonMetadataDecodable::ModuleWithStorage { prefix: lpre, module: lmod, storage: lstore },
				JsonMetadata::ModuleWithStorage { prefix: rpre, module: rmod, storage: rstore }
			) => {
				lpre == rpre && lmod == rmod && lstore == rstore
			},
			_ => false,
		}
    }
}
