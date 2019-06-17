#[macro_export]
macro_rules! impl_outer_error {
	(
		$(#[$attr:meta])*
		pub enum $name:ident {
			$( $modules:tt , )*
		}
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, $crate::codec::Encode, $crate::codec::Decode)]
		#[cfg_attr(feature = "std", derive(Debug, $crate::Serialize, $crate::Deserialize))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum $name {
			$(
				$modules( $modules::Error ),
			)*
		}
	}
}


#[macro_export]
macro_rules! decl_error {
	(
		$(#[$attr:meta])*
		pub enum Error {
			$(
				$errors:tt
			)*
		}
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq, $crate::codec::Encode)]
		#[cfg_attr(feature = "std", derive(Debug))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum Error {
			Unknown(&'static str),
			$(
				$errors
			)*
		}
		impl From<Error> for () {
			fn from(_: Error) -> () { () }
		}
		impl Into<u8> for Error {
			fn into(self) -> u8 {
				match self {
					Error::Unknown(_) => 0,
					_ => $crate::codec::Encode::using_encoded(&self, |s| s[0]),
				}
			}
		}

		impl From<&'static str> for Error {
			fn from(val: &'static str) -> Error {
				Error::Unknown(val)
			}
		}
	}
}
