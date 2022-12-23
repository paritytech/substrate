use crate::{Config, Event};
pub use alloc::{
	format,
	string::{String, ToString},
};
use codec::{Decode, Encode};
use ibc::core::ics26_routing::error::RouterError;
use sp_std::vec::Vec;

#[derive(
	PartialEq, Eq, Clone, frame_support::RuntimeDebug, scale_info::TypeInfo, Encode, Decode,
)]
pub enum IbcError {
	/// context error
	ContextError { message: Vec<u8> },
	/// unknown type URL
	UnknownMessageTypeUrl { message: Vec<u8> },
	/// the message is malformed and cannot be decoded
	MalformedMessageBytes { message: Vec<u8> },
}

impl From<RouterError> for IbcError {
	fn from(err: RouterError) -> Self {
		match err {
			RouterError::ContextError(e) =>
				IbcError::ContextError { message: e.to_string().as_bytes().to_vec() },
			RouterError::UnknownMessageTypeUrl { url } =>
				IbcError::UnknownMessageTypeUrl { message: url.as_bytes().to_vec() },
			RouterError::MalformedMessageBytes(e) =>
				IbcError::MalformedMessageBytes { message: e.to_string().as_bytes().to_vec() },
		}
	}
}

impl<T: Config> From<Vec<RouterError>> for Event<T> {
	fn from(errors: Vec<RouterError>) -> Self {
		let errors: Vec<IbcError> = errors.into_iter().map(|err| err.into()).collect();
		Event::<T>::IbcErrors { errors }
	}
}
