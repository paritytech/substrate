// Copyright 2018-2019 Parity Technologies (UK) Ltd.
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

//! Macros that define an Origin type. Every function call to your runtime has an origin which
//! specifies where the extrinsic was generated from.

/// Constructs an Origin type for a runtime. This is usually called automatically by the
/// construct_runtime macro. See also __create_decl_macro.
#[macro_export]
macro_rules! impl_outer_origin {

	// Macro transformations (to convert invocations with incomplete parameters to the canonical
	// form)

	(
		$(#[$attr:meta])*
		pub enum $name:ident for $runtime:ident {
			$( $module:ident $( <$generic:ident $(, $instance:path )? > )? ),* $(,)?
		}
	) => {
		$crate::impl_outer_origin! {
			$(#[$attr])*
			pub enum $name for $runtime where system = system {
				$( $module $( <$generic $(, $instance )? > )?, )*
			}
		}
	};
	(
		$(#[$attr:meta])*
		pub enum $name:ident for $runtime:ident where system = $system:ident {
			$( $module:ident $( <$generic:ident $(, $instance:path )?> )? ),* $(,)?
		}
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$runtime;
			$system;
			Modules { $( $module $( <$generic $(, $instance )? > )*, )* };
		);
	};

	// Replace generic param with runtime

	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		$system:ident;
		Modules {
			$module:ident $( <T $(,  $instance:path )? > )?,
			$( $rest_module:tt )*
		};
		$( $parsed:tt )*
	) => {
		$crate::impl_outer_origin!(
			$( #[$attr] )*;
			$name;
			$runtime;
			$system;
			Modules { $( $rest_module )* };
			$( $parsed )* $module $( <$runtime $(, $instance )? > )?,
		);
	};

	// The main macro expansion that actually renders the Origin enum code.

	(
		$(#[$attr:meta])*;
		$name:ident;
		$runtime:ident;
		$system:ident;
		Modules { };
		$( $module:ident $( <$generic_param:ident $(, $generic_instance:path )? > )* ,)*
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		$(#[$attr])*
		#[allow(non_camel_case_types)]
		pub enum $name {
			system($system::Origin<$runtime>),
			$(
				$module($module::Origin $( <$generic_param $(, $generic_instance )? > )* ),
			)*
			#[allow(dead_code)]
			Void($crate::Void)
		}
		#[allow(dead_code)]
		impl $name {
			pub const NONE: Self = $name::system($system::RawOrigin::None);
			pub const ROOT: Self = $name::system($system::RawOrigin::Root);
			pub fn signed(by: <$runtime as $system::Trait>::AccountId) -> Self {
				$name::system($system::RawOrigin::Signed(by))
			}
		}
		impl From<$system::Origin<$runtime>> for $name {
			fn from(x: $system::Origin<$runtime>) -> Self {
				$name::system(x)
			}
		}
		impl Into<$crate::rstd::result::Result<$system::Origin<$runtime>, $name>> for $name {
			fn into(self) -> $crate::rstd::result::Result<$system::Origin<$runtime>, Self> {
				if let $name::system(l) = self {
					Ok(l)
				} else {
					Err(self)
				}
			}
		}
		impl From<Option<<$runtime as $system::Trait>::AccountId>> for $name {
			fn from(x: Option<<$runtime as $system::Trait>::AccountId>) -> Self {
				<$system::Origin<$runtime>>::from(x).into()
			}
		}
		$(
			impl From<$module::Origin $( <$generic_param $(, $generic_instance )? > )*> for $name {
				fn from(x: $module::Origin $( <$generic_param $(, $generic_instance )? > )*) -> Self {
					$name::$module(x)
				}
			}
			impl Into<$crate::rstd::result::Result<
				$module::Origin $( <$generic_param $(, $generic_instance )? > )*,
				$name
			>> for $name {
				fn into(self) -> $crate::rstd::result::Result<
					$module::Origin $( <$generic_param $(, $generic_instance )? > )*,
					Self
				> {
					if let $name::$module(l) = self {
						Ok(l)
					} else {
						Err(self)
					}
				}
			}
		)*
	}
}

#[cfg(test)]
mod tests {
	mod system {
		pub trait Trait {
			type AccountId;
		}

		#[derive(Clone, PartialEq, Eq, Debug)]
		pub enum RawOrigin<AccountId> {
			Root,
			Signed(AccountId),
			None,
		}

		impl<AccountId> From<Option<AccountId>> for RawOrigin<AccountId> {
			fn from(s: Option<AccountId>) -> RawOrigin<AccountId> {
				match s {
					Some(who) => RawOrigin::Signed(who),
					None => RawOrigin::None,
				}
			}
		}

		pub type Origin<T> = RawOrigin<<T as Trait>::AccountId>;
	}

	mod origin_without_generic {
		#[derive(Clone, PartialEq, Eq, Debug)]
		pub struct Origin;
	}

	mod origin_with_generic {
		#[derive(Clone, PartialEq, Eq, Debug)]
		pub struct Origin<T> {
			t: T
		}
	}

	#[derive(Clone, PartialEq, Eq, Debug)]
	pub struct TestRuntime;

	impl system::Trait for TestRuntime {
		type AccountId = u32;
	}

	impl_outer_origin!(
		pub enum OriginWithoutSystem for TestRuntime {
			origin_without_generic,
			origin_with_generic<T>,
		}
	);

	impl_outer_origin!(
		pub enum OriginWithoutSystem2 for TestRuntime {
			origin_with_generic<T>,
			origin_without_generic
		}
	);

	impl_outer_origin!(
		pub enum OriginWithSystem for TestRuntime where system = system {
			origin_without_generic,
			origin_with_generic<T>
		}
	);

	impl_outer_origin!(
		pub enum OriginWithSystem2 for TestRuntime where system = system {
			origin_with_generic<T>,
			origin_without_generic,
		}
	);

	impl_outer_origin!(
		pub enum OriginEmpty for TestRuntime where system = system {}
	);
}
