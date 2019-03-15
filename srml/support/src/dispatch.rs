// Copyright 2017-2019 Parity Technologies (UK) Ltd.
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

//! Dispatch system. Contains a macro for defining runtime modules and
//! generating values representing lazy module function calls.

pub use crate::rstd::prelude::{Vec, Clone, Eq, PartialEq};
#[cfg(feature = "std")]
pub use std::fmt;
pub use crate::rstd::result;
pub use crate::codec::{Codec, Decode, Encode, Input, Output, HasCompact, EncodeAsRef};
pub use srml_metadata::{
	FunctionMetadata, DecodeDifferent, DecodeDifferentArray,
	FunctionArgumentMetadata, OuterDispatchMetadata, OuterDispatchCall
};

/// A type that can not be instantiated.
pub enum Never {}

/// Result of a module function call; either nothing (functions are only called for "side efeects")
/// or an error message.
pub type Result = result::Result<(), &'static str>;

/// A lazy call (module function and argument values) that can be executed via its dispatch()
/// method.
pub trait Dispatchable {
	/// Every function call to your runtime has an origin which specifies where the extrinsic was
	/// generated from. In the case of a signed extrinsic (transaction), the origin contains an
	/// identifier for the caller. The origin can be empty in the case of an inherent extrinsic.
	type Origin;
	type Trait;
	fn dispatch(self, origin: Self::Origin) -> Result;
}

/// Serializable version of Dispatchable.
/// This value can be used as a "function" in an extrinsic.
pub trait Callable {
	type Call: Dispatchable + Codec + Clone + PartialEq + Eq;
}

// dirty hack to work around serde_derive issue
// https://github.com/rust-lang/rust/issues/51331
pub type CallableCallFor<A> = <A as Callable>::Call;

#[cfg(feature = "std")]
pub trait Parameter: Codec + Clone + Eq + fmt::Debug {}

#[cfg(feature = "std")]
impl<T> Parameter for T where T: Codec + Clone + Eq + fmt::Debug {}

#[cfg(not(feature = "std"))]
pub trait Parameter: Codec + Clone + Eq {}

#[cfg(not(feature = "std"))]
impl<T> Parameter for T where T: Codec + Clone + Eq {}

/// Declare a module struct and implement the dispatch logic.
///
/// Usually used as follows:
///
/// decl_module! {
///		pub struct Module<T: Trait> for enum Call where origin: T::Origin
///{}
///	}
///
/// where "Trait" is a trait describing this module's requirements for the Runtime type.
/// T::Origin is declared using a impl_outer_origin! per-module macro (which is generated by the
/// construct_runtime! macro) and automatically includes all the modules that are used by the
/// runtime (alongside with a variant called "system").
///
/// A runtime module is a collection of functions unified by a common problem domain and certain
/// shared types. The "functions" do not actually return values (see Dispatchable) and are only
/// used for side effects.
///
/// For every module an associated enum (usually "Call") is generated with every variant
/// corresponding to a function of the module. This enum implements Callable and thus its values
/// can be used as an extrinsic's payload.
///
/// The `on_initialise` and `on_finalise` functions are special, since it can either take no
/// parameters, or one parameter, which has the runtime's block number type.
#[macro_export]
macro_rules! decl_module {
	// Macro transformations (to convert invocations with incomplete parameters to the canonical
	// form)
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty {
			$($t:tt)*
		}
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = system
			{}
			{}
			{}
			[]
			$($t)*
		);
	};
	(
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident {
			$($t:tt)*
		}
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{}
			{}
			{}
			[]
			$($t)*
		);
	};

	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{}
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event $(<$dpeg:ident>)* () = default;
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $vis fn deposit_event $(<$dpeg>)* () = default; }
			{ $( $on_initialise )* }
			{ $( $on_finalise )* }
			[ $($t)* ]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{}
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event $(<$dpeg:ident>)* (
			$($param_name:ident : $param:ty),*
		) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $vis fn deposit_event $(<$dpeg>)* ($( $param_name: $param ),* ) { $( $impl )* } }
			{ $( $on_initialise )* }
			{ $( $on_finalise )* }
			[ $($t)* ]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{}
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		fn on_finalise($($param_name:ident : $param:ty),* ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ $( $on_initialise )* }
			{ fn on_finalise( $( $param_name : $param ),* ) { $( $impl )* } }
			[ $($t)* ]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{}
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		fn on_initialise($($param_name:ident : $param:ty),* ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ fn on_initialise( $( $param_name : $param ),* ) { $( $impl )* } }
			{ $( $on_finalise )* }
			[ $($t)* ]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident(
			$origin:ident $(, $(#[$codec_attr:ident])* $param_name:ident : $param:ty)*
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ $( $on_initialise )* }
			{ $( $on_finalise )* }
			[
				$($t)*
				$(#[doc = $doc_attr])*
				$fn_vis fn $fn_name(
					$origin $( , $(#[$codec_attr])* $param_name : $param )*
				) $( -> $result )* { $( $impl )* }
			]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident(
			$origin:ident : T::Origin $(, $(#[$codec_attr:ident])* $param_name:ident : $param:ty)*
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"First parameter of dispatch should be marked `origin` only, with no type specified \
			(a bit like `self`). (For root-matching dispatches, ensure the first parameter does \
			not use the `T::Origin` type.)"
		)
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident(
			origin : $origin:ty $(, $(#[$codec_attr:ident])* $param_name:ident : $param:ty)*
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!(
			"First parameter of dispatch should be marked `origin` only, with no type specified \
			(a bit like `self`). (For root-matching dispatches, ensure the first parameter does \
			not use the `T::Origin` type.)"
		)
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident(
			$( $(#[$codec_attr:ident])* $param_name:ident : $param:ty),*
		) $( -> $result:ty )* { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ $( $on_initialise )* }
			{ $( $on_finalise )* }
			[
				$($t)*
				$(#[doc = $doc_attr])*
				$fn_vis fn $fn_name(
					root $( , $(#[$codec_attr])* $param_name : $param )*
				) $( -> $result )* { $( $impl )* }
			]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
	) => {
		decl_module!(@imp
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system {
				$($t)*
			}
			{ $( $deposit_event )* }
			{ $( $on_initialise )* }
			{ $( $on_finalise )* }
		);
	};

	// Implementation of Call enum's .dispatch() method.
	// TODO: this probably should be a different macro?

	(@call
		root
		$mod_type:ident $trait_instance:ident $fn_name:ident $origin:ident $system:ident [ $( $param_name:ident),* ]
	) => {
		{
			$system::ensure_root($origin)?;
			<$mod_type<$trait_instance>>::$fn_name( $( $param_name ),* )
		}
	};
	(@call
		$ingore:ident
		$mod_type:ident $trait_instance:ident $fn_name:ident $origin:ident $system:ident [ $( $param_name:ident),* ]
	) => {
		<$mod_type<$trait_instance>>::$fn_name( $origin $(, $param_name )* )
	};

	// no `deposit_event` function wanted
	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$system:ident;
	) => {};

	// Non-generic event
	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$system:ident;
		$vis:vis fn deposit_event() = default;
	) => {
		impl<$trait_instance: $trait_name> $module<$trait_instance> {
			$vis fn deposit_event(event: Event) {
				<$system::Module<$trait_instance>>::deposit_event(
					<$trait_instance as $trait_name>::Event::from(event).into()
				);
			}
		}
	};

	// Generic event
	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$system:ident;
		$vis:vis fn deposit_event<$ignore:ident>() = default;
	) => {
		impl<$trait_instance: $trait_name> $module<$trait_instance> {
			$vis fn deposit_event(event: Event<$trait_instance>) {
				<$system::Module<$trait_instance>>::deposit_event(
					<$trait_instance as $trait_name>::Event::from(event).into()
				);
			}
		}
	};

	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$system:ident;
		$vis:vis fn deposit_event($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name> $module<$trait_instance> {
			$vis fn deposit_event($param: $param_ty) {
				$( $impl )*
			}
		}
	};

	(@impl_on_initialise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_initialise() { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnInitialise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{
			fn on_initialise(_block_number_not_used: $trait_instance::BlockNumber) { $( $impl )* }
		}
	};

	(@impl_on_initialise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_initialise($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnInitialise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{
			fn on_initialise($param: $param_ty) { $( $impl )* }
		}
	};

	(@impl_on_initialise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnInitialise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{}
	};

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_finalise() { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{
			fn on_finalise(_block_number_not_used: $trait_instance::BlockNumber) { $( $impl )* }
		}
	};

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_finalise($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{
			fn on_finalise($param: $param_ty) { $( $impl )* }
		}
	};

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance>
		{
		}
	};

	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		root;
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn $name:ident ( root $(, $param:ident : $param_ty:ty )* ) { $( $impl:tt )* }
	) => {
		$(#[doc = $doc_attr])*
		$vis fn $name($( $param: $param_ty ),* ) -> $crate::dispatch::Result {
			{ $( $impl )* }
			Ok(())
		}
	};

	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		root;
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn $name:ident (
			root $(, $param:ident : $param_ty:ty )*
		) -> $result:ty { $( $impl:tt )* }
	) => {
		$(#[doc = $doc_attr])*
		$vis fn $name($( $param: $param_ty ),* ) -> $result {
			$( $impl )*
		}
	};

	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		$ignore:ident;
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn $name:ident (
			$origin:ident $(, $param:ident : $param_ty:ty )*
		) { $( $impl:tt )* }
	) => {
		$(#[doc = $doc_attr])*
		$vis fn $name(
			$origin: $origin_ty $(, $param: $param_ty )*
		) -> $crate::dispatch::Result {
			{ $( $impl )* }
			Ok(())
		}
	};

	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		$ignore:ident;
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn $name:ident (
			$origin:ident $(, $param:ident : $param_ty:ty )*
		) -> $result:ty { $( $impl:tt )* }
	) => {
		$(#[doc = $doc_attr])*
		$vis fn $name($origin: $origin_ty $(, $param: $param_ty )* ) -> $result {
			$( $impl )*
		}
	};

	// The main macro expansion that actually renders the module code.

	(@imp
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident {
			$(
				$(#[doc = $doc_attr:tt])*
				$fn_vis:vis fn $fn_name:ident(
					$from:ident $( , $(#[$codec_attr:ident])* $param_name:ident : $param:ty)*
				) $( -> $result:ty )* { $( $impl:tt )* }
			)*
		}
		{ $( $deposit_event:tt )* }
		{ $( $on_initialise:tt )* }
		{ $( $on_finalise:tt )* }
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		// FIXME: switching based on std feature is because of an issue in
		// serde-derive for when we attempt to derive `Deserialize` on these types,
		// in a situation where we've imported `srml_support` as another name.
		#[cfg(feature = "std")]
		pub struct $mod_type<$trait_instance: $trait_name>(::std::marker::PhantomData<$trait_instance>);

		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		#[cfg(not(feature = "std"))]
		pub struct $mod_type<$trait_instance: $trait_name>(::core::marker::PhantomData<$trait_instance>);

		decl_module! {
			@impl_on_initialise
			$mod_type<$trait_instance: $trait_name>;
			$( $on_initialise )*
		}

		decl_module! {
			@impl_on_finalise
			$mod_type<$trait_instance: $trait_name>;
			$( $on_finalise )*
		}

		decl_module! {
			@impl_deposit_event
			$mod_type<$trait_instance: $trait_name>;
			$system;
			$( $deposit_event )*
		}

		/// Can also be called using [`Call`].
		///
		/// [`Call`]: enum.Call.html
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			$(
				decl_module! {
					@impl_function
					$mod_type<$trait_instance: $trait_name>;
					$origin_type;
					$from;
					$(#[doc = $doc_attr])*
					$fn_vis fn $fn_name (
						$from $(, $param_name : $param )*
					) $( -> $result )* { $( $impl )* }
				}
			)*
		}

		#[cfg(feature = "std")]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			#[doc(hidden)]
			__PhantomItem(::std::marker::PhantomData<$trait_instance>, $crate::dispatch::Never),
			$(
				#[allow(non_camel_case_types)]
				$(#[doc = $doc_attr])*
				$fn_name ( $( $param ),* ),
			)*
		}

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			#[doc(hidden)]
			__PhantomItem(::core::marker::PhantomData<$trait_instance>, $crate::dispatch::Never),
			$(
				#[allow(non_camel_case_types)]
				$(#[doc = $doc_attr])*
				$fn_name ( $( $param ),* ),
			)*
		}

		// manual implementation of clone/eq/partialeq because using derive erroneously requires
		// clone/eq/partialeq from T.
		impl<$trait_instance: $trait_name> $crate::dispatch::Clone
			for $call_type<$trait_instance>
		{
			fn clone(&self) -> Self {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) =>
							$call_type::$fn_name( $( (*$param_name).clone() ),* )
					,)*
					_ => unreachable!(),
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::PartialEq
			for $call_type<$trait_instance>
		{
			fn eq(&self, _other: &Self) -> bool {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) => {
							let self_params = ( $( $param_name, )* );
							if let $call_type::$fn_name( $( ref $param_name ),* ) = *_other {
								self_params == ( $( $param_name, )* )
							} else {
								match *_other {
									$call_type::__PhantomItem(_, _) => unreachable!(),
									_ => false,
								}
							}
						}
					)*
					_ => unreachable!(),
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Eq
			for $call_type<$trait_instance>
		{}

		#[cfg(feature = "std")]
		impl<$trait_instance: $trait_name> $crate::dispatch::fmt::Debug
			for $call_type<$trait_instance>
		{
			fn fmt(&self, _f: &mut $crate::dispatch::fmt::Formatter) -> $crate::dispatch::result::Result<(), $crate::dispatch::fmt::Error> {
				match *self {
					$(
						$call_type::$fn_name( $( ref $param_name ),* ) =>
							write!(_f, "{}{:?}",
								stringify!($fn_name),
								( $( $param_name.clone(), )* )
							)
					,)*
					_ => unreachable!(),
				}
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Decode for $call_type<$trait_instance> {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				let _input_id = input.read_byte()?;
				$crate::__impl_decode!(input; _input_id; 0; $call_type; $( fn $fn_name( $( $(#[$codec_attr on type $param])* $param_name ),* ); )*)
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Encode for $call_type<$trait_instance> {
			fn encode_to<W: $crate::dispatch::Output>(&self, _dest: &mut W) {
				$crate::__impl_encode!(_dest; *self; 0; $call_type; $( fn $fn_name( $( $(#[$codec_attr on type $param])* $param_name ),* ); )*);
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Dispatchable
			for $call_type<$trait_instance>
		{
			type Trait = $trait_instance;
			type Origin = $origin_type;
			fn dispatch(self, _origin: Self::Origin) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$fn_name( $( $param_name ),* ) => {
							$crate::decl_module!(
								@call
								$from
								$mod_type $trait_instance $fn_name _origin $system [ $( $param_name ),* ]
							)
						},
					)*
					$call_type::__PhantomItem(_, _) => { unreachable!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Callable
			for $mod_type<$trait_instance>
		{
			type Call = $call_type<$trait_instance>;
		}

		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			#[doc(hidden)]
			pub fn dispatch<D: $crate::dispatch::Dispatchable<Trait = $trait_instance>>(d: D, origin: D::Origin) -> $crate::dispatch::Result {
				d.dispatch(origin)
			}
		}
		$crate::__dispatch_impl_metadata! {
			$mod_type $trait_instance $trait_name $call_type $origin_type
			{$( $(#[doc = $doc_attr])* fn $fn_name($from $(, $(#[$codec_attr])* $param_name : $param )*); )*}
		}
	}
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_decode {
	(
		$input:expr;
		$input_id:expr;
		$fn_id:expr;
		$call_type:ident;
		fn $fn_name:ident(
			$( $(#[$codec_attr:ident on type $param:ty])* $param_name:ident ),*
		);
		$($rest:tt)*
	) => {
		{
			if $input_id == ($fn_id) {
				$(
					$crate::__impl_decode!(@decode
						$(#[$codec_attr on type $param])*
						$param_name;
						$input;
					);
				)*
				return Some($call_type:: $fn_name( $( $param_name ),* ));
			}

			$crate::__impl_decode!($input; $input_id; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$input:expr;
		$input_id:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {
		None
	};
	(@decode
		#[compact on type $param:ty]
		$param_name:ident;
		$input:expr;
	) => {
		let $param_name = <<$param as $crate::dispatch::HasCompact>::Type as $crate::dispatch::Decode>::decode($input)?.into();
	};
	(@decode
		$param_name:ident;
		$input:expr;
	) => {
		let $param_name = $crate::dispatch::Decode::decode($input)?;
	};
	(@decode
		$(#[$codec_attr:ident on type])*
		$param_name:ident;
		$input:expr;
	) => {
		compile_error!(concat!(
			"Invalid attribute for parameter `",
			stringify!($param_name),
			"`, the following attributes are supported: `#[compact]`"
		))
	};
}

#[macro_export]
#[doc(hidden)]
macro_rules! __impl_encode {
	(
		$dest:expr;
		$self:expr;
		$fn_id:expr;
		$call_type:ident;
		fn $fn_name:ident(
			$( $(#[$codec_attr:ident on type $param:ty])* $param_name:ident ),*
		);
		$($rest:tt)*
	) => {
		{
			if let $call_type::$fn_name(
				$(
					ref $param_name
				),*
			) = $self {
				$dest.push_byte(($fn_id) as u8);
				$(
					$crate::__impl_encode!(@encode_as
						$(#[$codec_attr on type $param])*
						$param_name;
						$dest;
					);
				)*
			}

			$crate::__impl_encode!($dest; $self; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$dest:expr;
		$self:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {{}};
	(@encode_as
		#[compact on type $param:ty]
		$param_name:ident;
		$dest:expr;
	) => {
		<<$param as $crate::dispatch::HasCompact>::Type as $crate::dispatch::EncodeAsRef<$param>>::RefType::from($param_name).encode_to($dest);
	};
	(@encode_as
		$param_name:ident;
		$dest:expr;
	) => {
		$param_name.encode_to($dest);
	};
	(@encode_as
		$(#[$codec_attr:ident on type $param:ty])*
		$param_name:ident;
		$dest:expr;
	) => {
		compile_error!(concat!(
			"Invalid attribute for parameter `", stringify!($param_name),
			"`, the following attributes are supported: `#[compact]`"
		))
	};
}

pub trait IsSubType<T: Callable> {
	fn is_aux_sub_type(&self) -> Option<&<T as Callable>::Call>;
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
macro_rules! impl_outer_dispatch {
	(
		$(#[$attr:meta])*
		pub enum $call_type:ident for $runtime:ident where origin: $origin:ty {
			$(
				$module:ident::$camelcase:ident,
			)*
		}
	) => {
		$(#[$attr])*
		#[derive(Clone, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		pub enum $call_type {
			$(
				$camelcase ( $crate::dispatch::CallableCallFor<$camelcase> )
			,)*
		}
		$crate::__impl_outer_dispatch_common! { $call_type, $($camelcase,)* }
		impl $crate::dispatch::Dispatchable for $call_type {
			type Origin = $origin;
			type Trait = $call_type;
			fn dispatch(self, origin: $origin) -> $crate::dispatch::Result {
				match self {
					$(
						$call_type::$camelcase(call) => call.dispatch(origin),
					)*
				}
			}
		}
		$(
			impl $crate::dispatch::IsSubType<$camelcase> for $call_type {
				fn is_aux_sub_type(&self) -> Option<&<$camelcase as $crate::dispatch::Callable>::Call> {
					if let $call_type::$camelcase ( ref r ) = *self {
						Some(r)
					} else {
						None
					}
				}
			}
		)*
	}
}

/// Implement a meta-dispatch module to dispatch to other dispatchers.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_outer_dispatch_common {
	(
		$call_type:ident, $( $camelcase:ident, )*
	) => {
		impl $crate::dispatch::Decode for $call_type {
			fn decode<I: $crate::dispatch::Input>(input: &mut I) -> Option<Self> {
				let input_id = input.read_byte()?;
				$crate::__impl_decode!(input; input_id; 0; $call_type; $( fn $camelcase ( outer_dispatch_param ); )*)
			}
		}

		impl $crate::dispatch::Encode for $call_type {
			fn encode_to<W: $crate::dispatch::Output>(&self, dest: &mut W) {
				$crate::__impl_encode!(dest; *self; 0; $call_type; $( fn $camelcase( outer_dispatch_param ); )*)
			}
		}
	}
}

/// Implement metadata for dispatch.
#[macro_export]
#[doc(hidden)]
macro_rules! __dispatch_impl_metadata {
	(
		$mod_type:ident $trait_instance:ident $trait_name:ident
		$($rest:tt)*
	) => {
		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			#[doc(hidden)]
			pub fn call_functions() -> &'static [$crate::dispatch::FunctionMetadata] {
				$crate::__call_to_functions!($($rest)*)
			}
		}
	}
}

/// Convert the list of calls into their JSON representation, joined by ",".
#[macro_export]
#[doc(hidden)]
macro_rules! __call_to_functions {
	(
		$call_type:ident $origin_type:ty
			{$(
				$(#[doc = $doc_attr:tt])*
				fn $fn_name:ident($from:ident
					$(
						, $(#[$codec_attr:ident])* $param_name:ident : $param:ty
					)*
				);
			)*}
	) => {
		$crate::__functions_to_metadata!(0; $origin_type;; $(
			fn $fn_name( $($(#[$codec_attr])* $param_name: $param ),* );
			$( $doc_attr ),*;
		)*)
	};
}


/// Convert a list of functions into a list of `FunctionMetadata` items.
#[macro_export]
#[doc(hidden)]
macro_rules! __functions_to_metadata{
	(
		$fn_id:expr;
		$origin_type:ty;
		$( $function_metadata:expr ),*;
		fn $fn_name:ident(
			$(
				$(#[$codec_attr:ident])* $param_name:ident : $param:ty
			),*
		);
		$( $fn_doc:expr ),*;
		$( $rest:tt )*
	) => {
		$crate::__functions_to_metadata!(
			$fn_id + 1; $origin_type;
			$( $function_metadata, )* $crate::__function_to_metadata!(
				fn $fn_name($( $(#[$codec_attr])* $param_name : $param ),*); $( $fn_doc ),*; $fn_id;
			);
			$($rest)*
		)
	};
	(
		$fn_id:expr;
		$origin_type:ty;
		$( $function_metadata:expr ),*;
	) => {
		&[ $( $function_metadata ),* ]
	}
}

/// Convert a function into its metadata representation.
#[macro_export]
#[doc(hidden)]
macro_rules! __function_to_metadata {
	(
		fn $fn_name:ident(
			$( $(#[$codec_attr:ident])* $param_name:ident : $param:ty),*
		);
		$( $fn_doc:expr ),*;
		$fn_id:expr;
	) => {
		$crate::dispatch::FunctionMetadata {
			name: $crate::dispatch::DecodeDifferent::Encode(stringify!($fn_name)),
			arguments: $crate::dispatch::DecodeDifferent::Encode(&[
				$(
					$crate::dispatch::FunctionArgumentMetadata {
						name: $crate::dispatch::DecodeDifferent::Encode(stringify!($param_name)),
						ty: $crate::dispatch::DecodeDifferent::Encode(
							$crate::__function_to_metadata!(@stringify_expand_attr
								$(#[$codec_attr])* $param_name: $param
							)
						),
					}
				),*
			]),
			documentation: $crate::dispatch::DecodeDifferent::Encode(&[ $( $fn_doc ),* ]),
		}
	};

	(@stringify_expand_attr #[compact] $param_name:ident : $param:ty) => {
		concat!("Compact<", stringify!($param), ">")
	};

	(@stringify_expand_attr $param_name:ident : $param:ty) => { stringify!($param) };

	(@stringify_expand_attr $(#[codec_attr:ident])* $param_name:ident : $param:ty) => {
		compile_error!(concat!(
			"Invalid attribute for parameter `", stringify!($param_name),
			"`, the following attributes are supported: `#[compact]`"
		))
	}
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;
	use crate::runtime_primitives::traits::{OnInitialise, OnFinalise};

	pub trait Trait {
		type Origin;
		type BlockNumber: Into<u32>;
	}

	pub mod system {
		use super::Result;

		pub fn ensure_root<R>(_: R) -> Result {
			Ok(())
		}
	}

	decl_module! {
		pub struct Module<T: Trait> for enum Call where origin: T::Origin {
			/// Hi, this is a comment.
			fn aux_0(_origin) -> Result { unreachable!() }
			fn aux_1(_origin, #[compact] _data: u32) -> Result { unreachable!() }
			fn aux_2(_origin, _data: i32, _data2: String) -> Result { unreachable!() }
			fn aux_3() -> Result { unreachable!() }
			fn aux_4(_data: i32) -> Result { unreachable!() }

			fn on_initialise(n: T::BlockNumber) { if n.into() == 42 { panic!("on_initialise") } }
			fn on_finalise(n: T::BlockNumber) { if n.into() == 42 { panic!("on_finalise") } }
		}
	}

	const EXPECTED_METADATA: &'static [FunctionMetadata] = &[
				FunctionMetadata {
					name: DecodeDifferent::Encode("aux_0"),
					arguments: DecodeDifferent::Encode(&[]),
					documentation: DecodeDifferent::Encode(&[
						" Hi, this is a comment."
					])
				},
				FunctionMetadata {
					name: DecodeDifferent::Encode("aux_1"),
					arguments: DecodeDifferent::Encode(&[
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data"),
							ty: DecodeDifferent::Encode("Compact<u32>")
						}
					]),
					documentation: DecodeDifferent::Encode(&[]),
				},
				FunctionMetadata {
					name: DecodeDifferent::Encode("aux_2"),
					arguments: DecodeDifferent::Encode(&[
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data"),
							ty: DecodeDifferent::Encode("i32"),
						},
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data2"),
							ty: DecodeDifferent::Encode("String"),
						}
					]),
					documentation: DecodeDifferent::Encode(&[]),
				},
				FunctionMetadata {
					name: DecodeDifferent::Encode("aux_3"),
					arguments: DecodeDifferent::Encode(&[]),
					documentation: DecodeDifferent::Encode(&[]),
				},
				FunctionMetadata {
					name: DecodeDifferent::Encode("aux_4"),
					arguments: DecodeDifferent::Encode(&[
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data"),
							ty: DecodeDifferent::Encode("i32"),
						}
					]),
					documentation: DecodeDifferent::Encode(&[]),
				}
			];

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
	}

	#[test]
	fn module_json_metadata() {
		let metadata = Module::<TraitImpl>::call_functions();
		assert_eq!(EXPECTED_METADATA, metadata);
	}

	#[test]
	fn compact_attr() {
		let call: Call<TraitImpl> = Call::aux_1(0);
		let encoded = call.encode();
		assert_eq!(encoded.len(), 2);
	}

	#[test]
	#[should_panic(expected = "on_initialise")]
	fn on_initialise_should_work() {
		<Module<TraitImpl> as OnInitialise<u32>>::on_initialise(42);
	}

	#[test]
	#[should_panic(expected = "on_finalise")]
	fn on_finalise_should_work() {
		<Module<TraitImpl> as OnFinalise<u32>>::on_finalise(42);
	}
}
