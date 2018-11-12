// Copyright 2017-2018 Parity Technologies (UK) Ltd.
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

//! Dispatch system. Just dispatches calls.

pub use rstd::prelude::{Vec, Clone, Eq, PartialEq};
#[cfg(feature = "std")]
pub use std::fmt;
pub use rstd::result;
pub use codec::{Codec, Decode, Encode, Input, Output};
pub use srml_metadata::{
	ModuleMetadata, FunctionMetadata, DecodeDifferent,
	CallMetadata, FunctionArgumentMetadata, OuterDispatchMetadata, OuterDispatchCall
};

pub type Result = result::Result<(), &'static str>;

pub trait Dispatchable {
	type Origin;
	type Trait;
	fn dispatch(self, origin: Self::Origin) -> Result;
}

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

/// Declare a struct for this module, then implement dispatch logic to create a pairing of several
/// dispatch traits and enums.
#[macro_export]
macro_rules! decl_module {
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
			[]
			$($t)*
		);
	};

	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{}
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event() = default;
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $vis fn deposit_event() = default; }
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
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$vis:vis fn deposit_event($($param_name:ident : $param:ty),* ) { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $vis fn deposit_event($( $param_name: $param ),* ) { $( $impl )* } }
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
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident($origin:ident $(, $param_name:ident : $param:ty)* ) -> $result:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ $( $on_finalise )* }
			[
				$($t)*
				$(#[doc = $doc_attr])*
				$fn_vis fn $fn_name($origin $( , $param_name : $param )* ) -> $result { $( $impl )* }
			]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident($origin:ident : T::Origin $(, $param_name:ident : $param:ty)* ) -> $result:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("\
First parameter of dispatch should be marked `origin` only, with no\n\
type specified (a bit like `self`).\n\
(For root-matching dispatches, ensure the first parameter does not use\n\
the `T::Origin` type.)\
")
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident(origin : $origin:ty $(, $param_name:ident : $param:ty)* ) -> $result:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		compile_error!("\
First parameter of dispatch should be marked `origin` only, with no\n\
type specified (a bit like `self`).\n\
(For root-matching dispatches, ensure the first parameter is not named\n\
`origin`.)\
")
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
		{ $( $on_finalise:tt )* }
		[ $($t:tt)* ]
		$(#[doc = $doc_attr:tt])*
		$fn_vis:vis fn $fn_name:ident($( $param_name:ident : $param:ty),* ) -> $result:ty { $( $impl:tt )* }
		$($rest:tt)*
	) => {
		decl_module!(@normalize
			$(#[$attr])*
			pub struct $mod_type<$trait_instance: $trait_name>
			for enum $call_type where origin: $origin_type, system = $system
			{ $( $deposit_event )* }
			{ $( $on_finalise )* }
			[
				$($t)*
				$(#[doc = $doc_attr])*
				$fn_vis fn $fn_name(root $( , $param_name : $param )* ) -> $result { $( $impl )* }
			]
			$($rest)*
		);
	};
	(@normalize
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident
		{ $( $deposit_event:tt )* }
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
			{ $( $on_finalise )* }
		);
	};

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

	(@impl_deposit_event
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$system:ident;
		$vis:vis fn deposit_event() = default;
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

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_finalise() { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance> {
			fn on_finalise(_block_number_not_used: $trait_instance::BlockNumber) { $( $impl )* }
		}
	};

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		fn on_finalise($param:ident : $param_ty:ty) { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance> {
			fn on_finalise($param: $param_ty) { $( $impl )* }
		}
	};

	(@impl_on_finalise
		$module:ident<$trait_instance:ident: $trait_name:ident>;
	) => {
		impl<$trait_instance: $trait_name>
			$crate::runtime_primitives::traits::OnFinalise<$trait_instance::BlockNumber>
			for $module<$trait_instance> {}
	};

	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		root;
		$vis:vis fn $name:ident ( root $(, $param:ident : $param_ty:ty )* ) -> $result:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name> $module<$trait_instance> {
			$vis fn $name($( $param: $param_ty ),* ) -> $result {
				$( $impl )*
			}
		}
	};
	(@impl_function
		$module:ident<$trait_instance:ident: $trait_name:ident>;
		$origin_ty:ty;
		$ignore:ident;
		$vis:vis fn $name:ident ( $origin:ident $(, $param:ident : $param_ty:ty )* ) -> $result:ty { $( $impl:tt )* }
	) => {
		impl<$trait_instance: $trait_name> $module<$trait_instance> {
			$vis fn $name($origin: $origin_ty $(, $param: $param_ty )* ) -> $result {
				$( $impl )*
			}
		}
	};

	(@imp
		$(#[$attr:meta])*
		pub struct $mod_type:ident<$trait_instance:ident: $trait_name:ident>
		for enum $call_type:ident where origin: $origin_type:ty, system = $system:ident {
			$(
				$(#[doc = $doc_attr:tt])*
				$fn_vis:vis fn $fn_name:ident(
					$from:ident $( , $param_name:ident : $param:ty)*
				) -> $result:ty { $( $impl:tt )* }
			)*
		}
		{ $( $deposit_event:tt )* }
		{ $( $on_finalise:tt )* }
	) => {
		// Workaround for https://github.com/rust-lang/rust/issues/26925 . Remove when sorted.
		#[derive(Clone, Copy, PartialEq, Eq)]
		#[cfg_attr(feature = "std", derive(Debug))]
		// TODO: switching based on std feature is because of an issue in
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

		$(
			decl_module! {
				@impl_function
				$mod_type<$trait_instance: $trait_name>;
				$origin_type;
				$from;
				$fn_vis fn $fn_name ($from $(, $param_name : $param )* ) -> $result { $( $impl )* }
			}
		)*

		#[cfg(feature = "std")]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::std::marker::PhantomData<$trait_instance>),
			__OtherPhantomItem(::std::marker::PhantomData<$trait_instance>),
			$(
				#[allow(non_camel_case_types)]
				$fn_name ( $( $param ),* ),
			)*
		}

		#[cfg(not(feature = "std"))]
		$(#[$attr])*
		pub enum $call_type<$trait_instance: $trait_name> {
			__PhantomItem(::core::marker::PhantomData<$trait_instance>),
			__OtherPhantomItem(::core::marker::PhantomData<$trait_instance>),
			$(
				#[allow(non_camel_case_types)]
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
									$call_type::__PhantomItem(_) => unreachable!(),
									$call_type::__OtherPhantomItem(_) => unreachable!(),
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
				__impl_decode!(input; _input_id; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*)
			}
		}

		impl<$trait_instance: $trait_name> $crate::dispatch::Encode for $call_type<$trait_instance> {
			fn encode_to<W: $crate::dispatch::Output>(&self, _dest: &mut W) {
				__impl_encode!(_dest; *self; 0; $call_type; $( fn $fn_name( $( $param_name ),* ); )*);
				if let $call_type::__PhantomItem(_) = *self { unreachable!() }
				if let $call_type::__OtherPhantomItem(_) = *self { unreachable!() }
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
							decl_module!(
								@call
								$from
								$mod_type $trait_instance $fn_name _origin $system [ $( $param_name ),* ]
							)
						},
					)*
					_ => { panic!("__PhantomItem should never be used.") },
				}
			}
		}
		impl<$trait_instance: $trait_name> $crate::dispatch::Callable
			for $mod_type<$trait_instance>
		{
			type Call = $call_type<$trait_instance>;
		}

		impl<$trait_instance: $trait_name> $mod_type<$trait_instance> {
			pub fn dispatch<D: $crate::dispatch::Dispatchable<Trait = $trait_instance>>(d: D, origin: D::Origin) -> $crate::dispatch::Result {
				d.dispatch(origin)
			}
		}
		__dispatch_impl_metadata! {
			$mod_type $trait_instance $trait_name $call_type $origin_type
			{$( $(#[doc = $doc_attr])* fn $fn_name($from $(, $param_name : $param )*) -> $result; )*}
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
			$( $param_name:ident ),*
		);
		$($rest:tt)*
	) => {
		{
			if $input_id == ($fn_id) {
				$(
					let $param_name = $crate::dispatch::Decode::decode($input)?;
				)*
				return Some($call_type:: $fn_name( $( $param_name ),* ));
			}

			__impl_decode!($input; $input_id; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$input:expr;
		$input_id:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {
		None
	}
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
			$( $param_name:ident ),*
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
					$param_name.encode_to($dest);
				)*
			}

			__impl_encode!($dest; $self; $fn_id + 1; $call_type; $($rest)*)
		}
	};
	(
		$dest:expr;
		$self:expr;
		$fn_id:expr;
		$call_type:ident;
	) => {{}}
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
		__impl_outer_dispatch_common! { $call_type, $($camelcase,)* }
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
		__impl_outer_dispatch_metadata!($runtime; $call_type; $( $module::$camelcase, )*);
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
				__impl_decode!(input; input_id; 0; $call_type; $( fn $camelcase ( outer_dispatch_param ); )*)
			}
		}

		impl $crate::dispatch::Encode for $call_type {
			fn encode_to<W: $crate::dispatch::Output>(&self, dest: &mut W) {
				__impl_encode!(dest; *self; 0; $call_type; $( fn $camelcase( outer_dispatch_param ); )*)
			}
		}
	}
}

/// Implement metadata for outer dispatch.
#[macro_export]
#[doc(hidden)]
macro_rules! __impl_outer_dispatch_metadata {
	(
		$runtime:ident;
		$outer_name:ident;
		$( $module:ident::$call:ident, )*
	) => {
		impl $runtime {
			pub fn outer_dispatch_metadata() -> $crate::dispatch::OuterDispatchMetadata {
				$crate::dispatch::OuterDispatchMetadata {
					name: $crate::dispatch::DecodeDifferent::Encode(stringify!($outer_name)),
					calls: __impl_outer_dispatch_metadata!(@encode_calls 0; ; $( $module::$call, )*),
				}
			}
		}
	};
	(@encode_calls
		$index:expr;
		$( $encoded_call:expr ),*;
		$module:ident::$call:ident,
		$( $rest_module:ident::$rest:ident, )*
	) => {
		__impl_outer_dispatch_metadata!(
			@encode_calls
			$index + 1;
			$( $encoded_call, )*
			$crate::dispatch::OuterDispatchCall {
				name: $crate::dispatch::DecodeDifferent::Encode(stringify!($call)),
				prefix: $crate::dispatch::DecodeDifferent::Encode(stringify!($module)),
				index: $index,
			};
			$( $rest_module::$rest, )*
		)
	};
	(@encode_calls
		$index:expr;
		$( $encoded_call:expr ),*;
	) => {
		$crate::dispatch::DecodeDifferent::Encode(&[ $( $encoded_call ),* ])
	};
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
			pub fn metadata() -> $crate::dispatch::ModuleMetadata {
				$crate::dispatch::ModuleMetadata {
					name: $crate::dispatch::DecodeDifferent::Encode(stringify!($mod_type)),
					call: __call_to_metadata!($($rest)*),
				}
			}
		}
	}
}

/// Convert the list of calls into their JSON representation, joined by ",".
#[macro_export]
#[doc(hidden)]
macro_rules! __call_to_metadata {
	(
		$call_type:ident $origin_type:ty
			{$(
				$(#[doc = $doc_attr:tt])*
				fn $fn_name:ident($from:ident
					$(
						, $param_name:ident : $param:ty
					)*
				) -> $result:ty;
			)*}
	) => {
		$crate::dispatch::CallMetadata {
			name: $crate::dispatch::DecodeDifferent::Encode(stringify!($call_type)),
			functions: __functions_to_metadata!(0; $origin_type;; $(
				fn $fn_name( $( $param_name: $param ),* ) -> $result;
				$( $doc_attr ),*;
			)*),
		}
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
				$param_name:ident : $param:ty
			),*
		) -> $result:ty;
		$( $fn_doc:expr ),*;
		$( $rest:tt )*
	) => {
		__functions_to_metadata!(
			$fn_id + 1; $origin_type;
			$( $function_metadata, )* __function_to_metadata!(
				fn $fn_name($( $param_name : $param ),*) -> $result; $( $fn_doc ),*; $fn_id;
			);
			$($rest)*
		)
	};
	(
		$fn_id:expr;
		$origin_type:ty;
		$( $function_metadata:expr ),*;
	) => {
		$crate::dispatch::DecodeDifferent::Encode(&[ $( $function_metadata ),* ])
	}
}

/// Convert a function into its metadata representation.
#[macro_export]
#[doc(hidden)]
macro_rules! __function_to_metadata {
	(
		fn $fn_name:ident(
			$($param_name:ident : $param:ty),*
		) -> $result:ty;
		$( $fn_doc:expr ),*;
		$fn_id:expr;
	) => {
		$crate::dispatch::FunctionMetadata {
			id: $fn_id,
			name: $crate::dispatch::DecodeDifferent::Encode(stringify!($fn_name)),
			arguments: $crate::dispatch::DecodeDifferent::Encode(&[
				$(
					$crate::dispatch::FunctionArgumentMetadata {
						name: $crate::dispatch::DecodeDifferent::Encode(stringify!($param_name)),
						ty: $crate::dispatch::DecodeDifferent::Encode(stringify!($param)),
					}
				),*
			]),
			documentation: $crate::dispatch::DecodeDifferent::Encode(&[ $( $fn_doc ),* ]),
		}
	};
}

#[cfg(test)]
// Do not complain about unused `dispatch` and `dispatch_aux`.
#[allow(dead_code)]
mod tests {
	use super::*;

	pub trait Trait {
		type Origin;
		type BlockNumber;
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
			fn aux_1(_origin, _data: i32) -> Result { unreachable!() }
			fn aux_2(_origin, _data: i32, _data2: String) -> Result { unreachable!() }
			fn aux_3() -> Result { unreachable!() }
			fn aux_4(_data: i32) -> Result { unreachable!() }
		}
	}

	const EXPECTED_METADATA: ModuleMetadata = ModuleMetadata {
		name: DecodeDifferent::Encode("Module"),
		call: CallMetadata {
			name: DecodeDifferent::Encode("Call"),
			functions: DecodeDifferent::Encode(&[
				FunctionMetadata {
					id: 0,
					name: DecodeDifferent::Encode("aux_0"),
					arguments: DecodeDifferent::Encode(&[]),
					documentation: DecodeDifferent::Encode(&[
						" Hi, this is a comment."
					])
				},
				FunctionMetadata {
					id: 1,
					name: DecodeDifferent::Encode("aux_1"),
					arguments: DecodeDifferent::Encode(&[
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data"),
							ty: DecodeDifferent::Encode("i32"),
						}
					]),
					documentation: DecodeDifferent::Encode(&[]),
				},
				FunctionMetadata {
					id: 2,
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
					id: 3,
					name: DecodeDifferent::Encode("aux_3"),
					arguments: DecodeDifferent::Encode(&[]),
					documentation: DecodeDifferent::Encode(&[]),
				},
				FunctionMetadata {
					id: 4,
					name: DecodeDifferent::Encode("aux_4"),
					arguments: DecodeDifferent::Encode(&[
						FunctionArgumentMetadata {
							name: DecodeDifferent::Encode("_data"),
							ty: DecodeDifferent::Encode("i32"),
						}
					]),
					documentation: DecodeDifferent::Encode(&[]),
				}
			]),
		},
	};

	struct TraitImpl {}

	impl Trait for TraitImpl {
		type Origin = u32;
		type BlockNumber = u32;
	}

	#[test]
	fn module_json_metadata() {
		let metadata = Module::<TraitImpl>::metadata();
		assert_eq!(EXPECTED_METADATA, metadata);
	}
}
