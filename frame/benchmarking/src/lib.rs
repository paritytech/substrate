// Copyright 2020 Parity Technologies (UK) Ltd.
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

//! Macro for benchmarking a FRAME runtime.

#![cfg_attr(not(feature = "std"), no_std)]

mod tests;
mod utils;
#[cfg(feature = "std")]
mod analysis;

pub use utils::*;
#[cfg(feature = "std")]
pub use analysis::Analysis;
#[doc(hidden)]
pub use sp_io::storage::root as storage_root;
pub use sp_runtime::traits::{Dispatchable, Zero};
pub use paste;

/// Construct pallet benchmarks for weighing dispatchables.
///
/// Works around the idea of complexity parameters, named by a single letter (which is usually
/// upper cased in complexity notation but is lower-cased for use in this macro).
///
/// Complexity parameters ("parameters") have a range which is a `u32` pair. Every time a benchmark
/// is prepared and run, this parameter takes a concrete value within the range. There is an
/// associated instancing block, which is a single expression that is evaluated during
/// preparation. It may use `?` (`i.e. `return Err(...)`) to bail with a string error. Here's a
/// few examples:
///
/// ```ignore
/// // These two are equivalent:
/// let x in 0 .. 10;
/// let x in 0 .. 10 => ();
/// // This one calls a setup function and might return an error (which would be terminal).
/// let y in 0 .. 10 => setup(y)?;
/// // This one uses a code block to do lots of stuff:
/// let z in 0 .. 10 => {
///   let a = z * z / 5;
///   let b = do_something(a)?;
///   combine_into(z, b);
/// }
/// ```
///
/// Note that due to parsing restrictions, if the `from` expression is not a single token (i.e. a
/// literal or constant), then it must be parenthesised.
///
/// The macro allows for a number of "arms", each representing an individual benchmark. Using the
/// simple syntax, the associated dispatchable function maps 1:1 with the benchmark and the name of
/// the benchmark is the same as that of the associated function. However, extended syntax allows
/// for arbitrary expresions to be evaluated in a benchmark (including for example,
/// `on_initialize`).
///
/// The macro allows for common parameters whose ranges and instancing expressions may be drawn upon
/// (or not) by each arm. Syntax is available to allow for only the range to be drawn upon if
/// desired, allowing an alternative instancing expression to be given.
///
/// Note that the ranges are *inclusive* on both sides. This is in contrast to ranges in Rust which
/// are left-inclusive right-exclusive.
///
/// Each arm may also have a block of code which is run prior to any instancing and a block of code
/// which is run afterwards. All code blocks may draw upon the specific value of each parameter
/// at any time. Local variables are shared between the two pre- and post- code blocks, but do not
/// leak from the interior of any instancing expressions.
///
/// Any common parameters that are unused in an arm do not have their instancing expressions
/// evaluated.
///
/// Example:
/// ```ignore
/// benchmarks! {
///   // common parameter; just one for this example.
///   // will be `1`, `MAX_LENGTH` or any value inbetween
///   _ {
///     let l in 1 .. MAX_LENGTH => initialize_l(l);
///   }
///
///   // first dispatchable: foo; this is a user dispatchable and operates on a `u8` vector of
///   // size `l`, which we allow to be initialized as usual.
///   foo {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let l = ...;
///   }: _(Origin::Signed(caller), vec![0u8; l])
///
///   // second dispatchable: bar; this is a root dispatchable and accepts a `u8` vector of size
///   // `l`. We don't want it pre-initialized like before so we override using the `=> ()` notation.
///   // In this case, we explicitly name the call using `bar` instead of `_`.
///   bar {
///     let l = _ .. _ => ();
///   }: bar(Origin::Root, vec![0u8; l])
///
///   // third dispatchable: baz; this is a user dispatchable. It isn't dependent on length like the
///   // other two but has its own complexity `c` that needs setting up. It uses `caller` (in the
///   // pre-instancing block) within the code block. This is only allowed in the param instancers
///   // of arms. Instancers of common params cannot optimistically draw upon hypothetical variables
///   // that the arm's pre-instancing code block might have declared.
///   baz1 {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let c = 0 .. 10 => setup_c(&caller, c);
///   }: baz(Origin::Signed(caller))
///
///   // this is a second benchmark of the baz dispatchable with a different setup.
///   baz2 {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let c = 0 .. 10 => setup_c_in_some_other_way(&caller, c);
///   }: baz(Origin::Signed(caller))
///
///   // this is benchmarking some code that is not a dispatchable.
///   populate_a_set {
///     let x in 0 .. 10_000;
///     let mut m = Vec::<u32>::new();
///     for i in 0..x {
///       m.insert(i);
///     }
///   }: { m.into_iter().collect::<BTreeSet>() }
/// }
/// ```
///
/// Test functions are automatically generated for each benchmark and are accessible to you when you
/// run `cargo test`. All tests are named `test_benchmark_<benchmark_name>`, expect you to pass them
/// the Runtime Trait, and run them in a test externalities environment. The test function runs your
/// benchmark just like a regular benchmark, but only testing at the lowest and highest values for
/// each component. The function will return `Ok(())` if the benchmarks return no errors.
///
/// You can optionally add a `verify` code block at the end of a benchmark to test any final state
/// of your benchmark in a unit test. For example:
///
/// ```ignore
/// sort_vector {
/// 	let x in 1 .. 10000;
/// 	let mut m = Vec::<u32>::new();
/// 	for i in (0..x).rev() {
/// 		m.push(i);
/// 	}
/// }: {
/// 	m.sort();
/// } verify {
/// 	ensure!(m[0] == 0, "You forgot to sort!")
/// }
/// ```
///
/// These `verify` blocks will not execute when running your actual benchmarks!
///
/// You can construct benchmark tests like so:
///
/// ```ignore
/// #[test]
/// fn test_benchmarks() {
///   new_test_ext().execute_with(|| {
///     assert_ok!(test_benchmark_dummy::<Test>());
///     assert_err!(test_benchmark_other_name::<Test>(), "Bad origin");
///     assert_ok!(test_benchmark_sort_vector::<Test>());
///     assert_err!(test_benchmark_broken_benchmark::<Test>(), "You forgot to sort!");
///   });
/// }
/// ```
#[macro_export]
macro_rules! benchmarks {
	(
		_ {
			$(
				let $common:ident in $common_from:tt .. $common_to:expr => $common_instancer:expr;
			)*
		}
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter!(
			NO_INSTANCE
			{ $( { $common , $common_from , $common_to , $common_instancer } )* }
			( )
			$( $rest )*
		);
	}
}

#[macro_export]
macro_rules! benchmarks_instance {
	(
		_ {
			$(
				let $common:ident in $common_from:tt .. $common_to:expr => $common_instancer:expr;
			)*
		}
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter!(
			INSTANCE
			{ $( { $common , $common_from , $common_to , $common_instancer } )* }
			( )
			$( $rest )*
		);
	}
}

#[macro_export]
#[allow(missing_docs)]
macro_rules! benchmarks_iter {
	// mutation arm:
	(
		$instance:ident
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: _ ( $origin:expr $( , $arg:expr )* )
		verify $postcode:block
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			$instance
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: $name ( $origin $( , $arg )* )
			verify $postcode
			$( $rest )*
		}
	};
	// no instance mutation arm:
	(
		NO_INSTANCE
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $dispatch:ident ( $origin:expr $( , $arg:expr )* )
		verify $postcode:block
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			NO_INSTANCE
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: {
				<Call<T> as $crate::Dispatchable>::dispatch(Call::<T>::$dispatch($($arg),*), $origin.into())?;
			}
			verify $postcode
			$( $rest )*
		}
	};
	// instance mutation arm:
	(
		INSTANCE
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $dispatch:ident ( $origin:expr $( , $arg:expr )* )
		verify $postcode:block
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			INSTANCE
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: {
				<Call<T, I> as $crate::Dispatchable>::dispatch(Call::<T, I>::$dispatch($($arg),*), $origin.into())?;
			}
			verify $postcode
			$( $rest )*
		}
	};
	// iteration arm:
	(
		$instance:ident
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $eval:block
		verify $postcode:block
		$( $rest:tt )*
	) => {
		$crate::benchmark_backend! {
			$instance
			$name
			{ $( $common )* }
			{ }
			{ $eval }
			{ $( $code )* }
			$postcode
		}
		$crate::benchmarks_iter!(
			$instance
			{ $( $common )* }
			( $( $names )* $name )
			$( $rest )*
		);
	};
	// iteration-exit arm
	( $instance:ident { $( $common:tt )* } ( $( $names:ident )* ) ) => {
		$crate::selected_benchmark!( $instance $( $names ),* );
		$crate::impl_benchmark!( $instance $( $names ),* );
		#[cfg(test)]
		$crate::impl_benchmark_tests!( $instance $( $names ),* );
	};
	// add verify block to _() format
	(
		$instance:ident
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: _ ( $origin:expr $( , $arg:expr )* )
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			$instance
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: _ ( $origin $( , $arg )* )
			verify { }
			$( $rest )*
		}
	};
	// add verify block to name() format
	(
		$instance:ident
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $dispatch:ident ( $origin:expr $( , $arg:expr )* )
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			$instance
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: $dispatch ( $origin $( , $arg )* )
			verify { }
			$( $rest )*
		}
	};
	// add verify block to {} format
	(
		$instance:ident
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $eval:block
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter!(
			$instance
			{ $( $common )* }
			( $( $names )* )
			$name { $( $code )* }: $eval
			verify { }
			$( $rest )*
		);
	};
}

#[macro_export]
#[allow(missing_docs)]
macro_rules! benchmark_backend {
	// parsing arms
	($instance:ident $name:ident {
		$( $common:tt )*
	} {
		$( PRE { $( $pre_parsed:tt )* } )*
	} { $eval:block } {
			let $pre_id:tt : $pre_ty:ty = $pre_ex:expr;
			$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name { $( $common )* } {
				$( PRE { $( $pre_parsed )* } )*
				PRE { $pre_id , $pre_ty , $pre_ex }
			} { $eval } { $( $rest )* } $postcode
		}
	};
	($instance:ident $name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $param:ident in ( $param_from:expr ) .. $param_to:expr => $param_instancer:expr;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name { $( $common )* } {
				$( $parsed )*
				PARAM { $param , $param_from , $param_to , $param_instancer }
			} { $eval } { $( $rest )* } $postcode
		}
	};
	// mutation arm to look after defaulting to a common param
	($instance:ident $name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $param:ident in ...;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name {
				$( { $common , $common_from , $common_to , $common_instancer } )*
			} {
				$( $parsed )*
			} { $eval } {
				let $param
					in ({ $( let $common = $common_from; )* $param })
					.. ({ $( let $common = $common_to; )* $param })
					=> ({ $( let $common = || -> Result<(), &'static str> { $common_instancer ; Ok(()) }; )* $param()? });
				$( $rest )*
			} $postcode
		}
	};
	// mutation arm to look after defaulting only the range to common param
	($instance:ident $name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $param:ident in _ .. _ => $param_instancer:expr ;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name {
				$( { $common , $common_from , $common_to , $common_instancer } )*
			} {
				$( $parsed )*
			} { $eval } {
				let $param
					in ({ $( let $common = $common_from; )* $param })
					.. ({ $( let $common = $common_to; )* $param })
					=> $param_instancer ;
				$( $rest )*
			} $postcode
		}
	};
	// mutation arm to look after a single tt for param_from.
	($instance:ident $name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $param:ident in $param_from:tt .. $param_to:expr => $param_instancer:expr ;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name { $( $common )* } { $( $parsed )* } { $eval } {
				let $param in ( $param_from ) .. $param_to => $param_instancer;
				$( $rest )*
			} $postcode
		}
	};
	// mutation arm to look after the default tail of `=> ()`
	($instance:ident $name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $param:ident in $param_from:tt .. $param_to:expr;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name { $( $common )* } { $( $parsed )* } { $eval } {
				let $param in $param_from .. $param_to => ();
				$( $rest )*
			} $postcode
		}
	};
	// mutation arm to look after `let _ =`
	($instance:ident $name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:block } {
		let $pre_id:tt = $pre_ex:expr;
		$( $rest:tt )*
	} $postcode:block) => {
		$crate::benchmark_backend! {
			$instance $name { $( $common )* } { $( $parsed )* } { $eval } {
				let $pre_id : _ = $pre_ex;
				$( $rest )*
			} $postcode
		}
	};
	// no instance actioning arm
	(NO_INSTANCE $name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( PRE { $pre_id:tt , $pre_ty:ty , $pre_ex:expr } )*
		$( PARAM { $param:ident , $param_from:expr , $param_to:expr , $param_instancer:expr } )*
	} { $eval:block } { $( $post:tt )* } $postcode:block) => {
		#[allow(non_camel_case_types)]
		struct $name;
		#[allow(unused_variables)]
		impl<T: Trait> $crate::BenchmarkingSetup<T> for $name {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				vec! [
					$(
						($crate::BenchmarkParameter::$param, $param_from, $param_to)
					),*
				]
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				$(
					let $common = $common_from;
				)*
				$(
					// Prepare instance
					let $param = components.iter().find(|&c| c.0 == $crate::BenchmarkParameter::$param).unwrap().1;
				)*
				$(
					let $pre_id : $pre_ty = $pre_ex;
				)*
				$( $param_instancer ; )*
				$( $post )*

				Ok(Box::new(move || -> Result<(), &'static str> { $eval; Ok(()) }))
			}

			fn verify(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				$(
					let $common = $common_from;
				)*
				$(
					// Prepare instance
					let $param = components.iter().find(|&c| c.0 == $crate::BenchmarkParameter::$param).unwrap().1;
				)*
				$(
					let $pre_id : $pre_ty = $pre_ex;
				)*
				$( $param_instancer ; )*
				$( $post )*

				Ok(Box::new(move || -> Result<(), &'static str> { $eval; $postcode; Ok(()) }))
			}
		}
	};
	// instance actioning arm
	(INSTANCE $name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( PRE { $pre_id:tt , $pre_ty:ty , $pre_ex:expr } )*
		$( PARAM { $param:ident , $param_from:expr , $param_to:expr , $param_instancer:expr } )*
	} { $eval:block } { $( $post:tt )* } $postcode:block) => {
		#[allow(non_camel_case_types)]
		struct $name;
		#[allow(unused_variables)]
		impl<T: Trait<I>, I: Instance> $crate::BenchmarkingSetupInstance<T, I> for $name {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				vec! [
					$(
						($crate::BenchmarkParameter::$param, $param_from, $param_to)
					),*
				]
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				$(
					let $common = $common_from;
				)*
				$(
					// Prepare instance
					let $param = components.iter().find(|&c| c.0 == $crate::BenchmarkParameter::$param).unwrap().1;
				)*
				$(
					let $pre_id : $pre_ty = $pre_ex;
				)*
				$( $param_instancer ; )*
				$( $post )*

				Ok(Box::new(move || -> Result<(), &'static str> { $eval; Ok(()) }))
			}

			fn verify(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				$(
					let $common = $common_from;
				)*
				$(
					// Prepare instance
					let $param = components.iter().find(|&c| c.0 == $crate::BenchmarkParameter::$param).unwrap().1;
				)*
				$(
					let $pre_id : $pre_ty = $pre_ex;
				)*
				$( $param_instancer ; )*
				$( $post )*

				Ok(Box::new(move || -> Result<(), &'static str> { $eval; $postcode; Ok(()) }))
			}
		}
	}
}

/// Creates a `SelectedBenchmark` enum implementing `BenchmarkingSetup`.
///
/// Every variant must implement [`BenchmarkingSetup`].
///
/// ```nocompile
///
/// struct Transfer;
/// impl BenchmarkingSetup for Transfer { ... }
///
/// struct SetBalance;
/// impl BenchmarkingSetup for SetBalance { ... }
///
/// selected_benchmark!(Transfer, SetBalance);
/// ```
#[macro_export]
macro_rules! selected_benchmark {
	(
		NO_INSTANCE $( $bench:ident ),*
	) => {
		// The list of available benchmarks for this pallet.
		#[allow(non_camel_case_types)]
		enum SelectedBenchmark {
			$( $bench, )*
		}

		// Allow us to select a benchmark from the list of available benchmarks.
		impl<T: Trait> $crate::BenchmarkingSetup<T> for SelectedBenchmark {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<T>>::components(&$bench), )*
				}
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<T>>::instance(&$bench, components), )*
				}
			}

			fn verify(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<T>>::verify(&$bench, components), )*
				}
			}
		}
	};
	(
		INSTANCE $( $bench:ident ),*
	) => {
		// The list of available benchmarks for this pallet.
		#[allow(non_camel_case_types)]
		enum SelectedBenchmark {
			$( $bench, )*
		}

		// Allow us to select a benchmark from the list of available benchmarks.
		impl<T: Trait<I>, I: Instance> $crate::BenchmarkingSetupInstance<T, I> for SelectedBenchmark {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetupInstance<T, I>>::components(&$bench), )*
				}
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetupInstance<T, I>>::instance(&$bench, components), )*
				}
			}

			fn verify(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<Box<dyn FnOnce() -> Result<(), &'static str>>, &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetupInstance<T, I>>::verify(&$bench, components), )*
				}
			}
		}
	}
}

#[macro_export]
macro_rules! impl_benchmark {
	(
		NO_INSTANCE $( $name:ident ),*
	) => {
		impl<T: Trait> $crate::Benchmarking<$crate::BenchmarkResults> for Module<T>
			where T: frame_system::Trait
		{
			fn benchmarks() -> Vec<&'static [u8]> {
				vec![ $( stringify!($name).as_ref() ),* ]
			}

			fn run_benchmark(
				extrinsic: &[u8],
				lowest_range_values: &[u32],
				highest_range_values: &[u32],
				steps: &[u32],
				repeat: u32,
			) -> Result<Vec<$crate::BenchmarkResults>, &'static str> {
				// Map the input to the selected benchmark.
				let extrinsic = sp_std::str::from_utf8(extrinsic)
					.map_err(|_| "`extrinsic` is not a valid utf8 string!")?;
				let selected_benchmark = match extrinsic {
					$( stringify!($name) => SelectedBenchmark::$name, )*
					_ => return Err("Could not find extrinsic."),
				};

				// Warm up the DB
				$crate::benchmarking::commit_db();
				$crate::benchmarking::wipe_db();

				let components = <SelectedBenchmark as $crate::BenchmarkingSetup<T>>::components(&selected_benchmark);
				let mut results: Vec<$crate::BenchmarkResults> = Vec::new();

				// Default number of steps for a component.
				let mut prev_steps = 10;

				// Select the component we will be benchmarking. Each component will be benchmarked.
				for (idx, (name, low, high)) in components.iter().enumerate() {
					// Get the number of steps for this component.
					let steps = steps.get(idx).cloned().unwrap_or(prev_steps);
					prev_steps = steps;

					// Skip this loop if steps is zero
					if steps == 0 { continue }

					let lowest = lowest_range_values.get(idx).cloned().unwrap_or(*low);
					let highest = highest_range_values.get(idx).cloned().unwrap_or(*high);

					let diff = highest - lowest;

					// Create up to `STEPS` steps for that component between high and low.
					let step_size = (diff / steps).max(1);
					let num_of_steps = diff / step_size + 1;

					for s in 0..num_of_steps {
						// This is the value we will be testing for component `name`
						let component_value = lowest + step_size * s;

						// Select the max value for all the other components.
						let c: Vec<($crate::BenchmarkParameter, u32)> = components.iter()
							.enumerate()
							.map(|(idx, (n, _, h))|
								if n == name {
									(*n, component_value)
								} else {
									(*n, *highest_range_values.get(idx).unwrap_or(h))
								}
							)
							.collect();

						// Run the benchmark `repeat` times.
						for _ in 0..repeat {
							// Set up the externalities environment for the setup we want to benchmark.
							let closure_to_benchmark = <SelectedBenchmark as $crate::BenchmarkingSetup<T>>::instance(&selected_benchmark, &c)?;

							// Set the block number to at least 1 so events are deposited.
							if $crate::Zero::is_zero(&frame_system::Module::<T>::block_number()) {
								frame_system::Module::<T>::set_block_number(1.into());
							}

							// Commit the externalities to the database, flushing the DB cache.
							// This will enable worst case scenario for reading from the database.
							$crate::benchmarking::commit_db();

							// Time the extrinsic logic.
							frame_support::debug::trace!(target: "benchmark", "Start Benchmark: {:?} {:?}", name, component_value);
							let start_extrinsic = $crate::benchmarking::current_time();
							closure_to_benchmark()?;
							let finish_extrinsic = $crate::benchmarking::current_time();
							let elapsed_extrinsic = finish_extrinsic - start_extrinsic;
							frame_support::debug::trace!(target: "benchmark", "End Benchmark: {} ns", elapsed_extrinsic);

							// Time the storage root recalculation.
							let start_storage_root = $crate::benchmarking::current_time();
							$crate::storage_root();
							let finish_storage_root = $crate::benchmarking::current_time();
							let elapsed_storage_root = finish_storage_root - start_storage_root;

							results.push((c.clone(), elapsed_extrinsic, elapsed_storage_root));

							// Wipe the DB back to the genesis state.
							$crate::benchmarking::wipe_db();
						}
					}
				}
				return Ok(results);
			}
		}
	};
	(
		INSTANCE $( $name:ident ),*
	) => {
		impl<T: Trait<I>, I: Instance> $crate::Benchmarking<$crate::BenchmarkResults> for Module<T, I>
			where T: frame_system::Trait
		{
			fn benchmarks() -> Vec<&'static [u8]> {
				vec![ $( stringify!($name).as_ref() ),* ]
			}

			fn run_benchmark(
				extrinsic: &[u8],
				lowest_range_values: &[u32],
				highest_range_values: &[u32],
				steps: &[u32],
				repeat: u32,
			) -> Result<Vec<$crate::BenchmarkResults>, &'static str> {
				// Map the input to the selected benchmark.
				let extrinsic = sp_std::str::from_utf8(extrinsic)
					.map_err(|_| "`extrinsic` is not a valid utf8 string!")?;
				let selected_benchmark = match extrinsic {
					$( stringify!($name) => SelectedBenchmark::$name, )*
					_ => return Err("Could not find extrinsic."),
				};

				// Warm up the DB
				$crate::benchmarking::commit_db();
				$crate::benchmarking::wipe_db();

				let components = <SelectedBenchmark as $crate::BenchmarkingSetupInstance<T, I>>::components(&selected_benchmark);
				let mut results: Vec<$crate::BenchmarkResults> = Vec::new();

				// Default number of steps for a component.
				let mut prev_steps = 10;

				// Select the component we will be benchmarking. Each component will be benchmarked.
				for (idx, (name, low, high)) in components.iter().enumerate() {
					// Get the number of steps for this component.
					let steps = steps.get(idx).cloned().unwrap_or(prev_steps);
					prev_steps = steps;

					// Skip this loop if steps is zero
					if steps == 0 { continue }

					let lowest = lowest_range_values.get(idx).cloned().unwrap_or(*low);
					let highest = highest_range_values.get(idx).cloned().unwrap_or(*high);

					let diff = highest - lowest;

					// Create up to `STEPS` steps for that component between high and low.
					let step_size = (diff / steps).max(1);
					let num_of_steps = diff / step_size + 1;

					for s in 0..num_of_steps {
						// This is the value we will be testing for component `name`
						let component_value = lowest + step_size * s;

						// Select the max value for all the other components.
						let c: Vec<($crate::BenchmarkParameter, u32)> = components.iter()
							.enumerate()
							.map(|(idx, (n, _, h))|
								if n == name {
									(*n, component_value)
								} else {
									(*n, *highest_range_values.get(idx).unwrap_or(h))
								}
							)
							.collect();

						// Run the benchmark `repeat` times.
						for _ in 0..repeat {
							// Set up the externalities environment for the setup we want to benchmark.
							let closure_to_benchmark = <SelectedBenchmark as $crate::BenchmarkingSetupInstance<T, I>>::instance(&selected_benchmark, &c)?;

							// Set the block number to at least 1 so events are deposited.
							if $crate::Zero::is_zero(&frame_system::Module::<T>::block_number()) {
								frame_system::Module::<T>::set_block_number(1.into());
							}

							// Commit the externalities to the database, flushing the DB cache.
							// This will enable worst case scenario for reading from the database.
							$crate::benchmarking::commit_db();

							// Time the extrinsic logic.
							frame_support::debug::trace!(target: "benchmark", "Start Benchmark: {:?} {:?}", name, component_value);
							let start_extrinsic = $crate::benchmarking::current_time();
							closure_to_benchmark()?;
							let finish_extrinsic = $crate::benchmarking::current_time();
							let elapsed_extrinsic = finish_extrinsic - start_extrinsic;
							frame_support::debug::trace!(target: "benchmark", "End Benchmark: {} ns", elapsed_extrinsic);

							// Time the storage root recalculation.
							let start_storage_root = $crate::benchmarking::current_time();
							$crate::storage_root();
							let finish_storage_root = $crate::benchmarking::current_time();
							let elapsed_storage_root = finish_storage_root - start_storage_root;

							results.push((c.clone(), elapsed_extrinsic, elapsed_storage_root));

							// Wipe the DB back to the genesis state.
							$crate::benchmarking::wipe_db();
						}
					}
				}
				return Ok(results);
			}
		}
	}
}

// This creates unit tests from the main benchmark macro.
// They run the benchmark using the `high` and `low` value for each component
// and ensure that everything completes successfully.
#[macro_export]
macro_rules! impl_benchmark_tests {
	(
		NO_INSTANCE
		$( $name:ident ),*
	) => {
		$(
			$crate::paste::item! {
				fn [<test_benchmark_ $name>] <T: Trait> () -> Result<(), &'static str>
					where T: frame_system::Trait
				{
					let selected_benchmark = SelectedBenchmark::$name;
					let components = <SelectedBenchmark as $crate::BenchmarkingSetup<T>>::components(&selected_benchmark);

					for (_, (name, low, high)) in components.iter().enumerate() {
						// Test only the low and high value, assuming values in the middle won't break
						for component_value in vec![low, high] {
							// Select the max value for all the other components.
							let c: Vec<($crate::BenchmarkParameter, u32)> = components.iter()
								.enumerate()
								.map(|(_, (n, _, h))|
									if n == name {
										(*n, *component_value)
									} else {
										(*n, *h)
									}
								)
								.collect();

							// Set up the verification state
							let closure_to_verify = <SelectedBenchmark as $crate::BenchmarkingSetup<T>>::verify(&selected_benchmark, &c)?;

							// Set the block number to at least 1 so events are deposited.
							if $crate::Zero::is_zero(&frame_system::Module::<T>::block_number()) {
								frame_system::Module::<T>::set_block_number(1.into());
							}

							// Run verification
							closure_to_verify()?;

							// Reset the state
							$crate::benchmarking::wipe_db();
						}
					}
					Ok(())
				}
			}
		)*
	};
	(
		INSTANCE
		$( $name:ident ),*
	) => {
		$(
			$crate::paste::item! {
				fn [<test_benchmark_ $name>] <T: Trait> () -> Result<(), &'static str>
					where T: frame_system::Trait
				{
					let selected_benchmark = SelectedBenchmark::$name;
					let components = <SelectedBenchmark as $crate::BenchmarkingSetupInstance<T, _>>::components(&selected_benchmark);

					for (_, (name, low, high)) in components.iter().enumerate() {
						// Test only the low and high value, assuming values in the middle won't break
						for component_value in vec![low, high] {
							// Select the max value for all the other components.
							let c: Vec<($crate::BenchmarkParameter, u32)> = components.iter()
								.enumerate()
								.map(|(_, (n, _, h))|
									if n == name {
										(*n, *component_value)
									} else {
										(*n, *h)
									}
								)
								.collect();

							// Set up the verification state
							let closure_to_verify = <SelectedBenchmark as $crate::BenchmarkingSetupInstance<T, _>>::verify(&selected_benchmark, &c)?;

							// Set the block number to at least 1 so events are deposited.
							if $crate::Zero::is_zero(&frame_system::Module::<T>::block_number()) {
								frame_system::Module::<T>::set_block_number(1.into());
							}

							// Run verification
							closure_to_verify()?;

							// Reset the state
							$crate::benchmarking::wipe_db();
						}
					}
					Ok(())
				}
			}
		)*
	};
}


/// This macro adds pallet benchmarks to a `Vec<BenchmarkBatch>` object.
///
/// First create an object that holds in the input parameters for the benchmark:
///
/// ```ignore
/// let params = (&pallet, &benchmark, &lowest_range_values, &highest_range_values, &steps, repeat);
/// ```
///
/// Then define a mutable local variable to hold your `BenchmarkBatch` object:
///
/// ```ignore
/// let mut batches = Vec::<BenchmarkBatch>::new();
/// ````
///
/// Then add the pallets you want to benchmark to this object, including the string
/// you want to use target a particular pallet:
///
/// ```ignore
/// add_benchmark!(params, batches, b"balances", Balances);
/// add_benchmark!(params, batches, b"identity", Identity);
/// add_benchmark!(params, batches, b"session", SessionBench::<Runtime>);
/// ...
/// ```
///
/// At the end of `dispatch_benchmark`, you should return this batches object.
#[macro_export]
macro_rules! add_benchmark {
	( $params:ident, $batches:ident, $name:literal, $( $location:tt )* ) => (
		let (pallet, benchmark, lowest_range_values, highest_range_values, steps, repeat) = $params;
		if &pallet[..] == &$name[..] || &pallet[..] == &b"*"[..] {
			if &pallet[..] == &b"*"[..] || &benchmark[..] == &b"*"[..] {
				for benchmark in $( $location )*::benchmarks().into_iter() {
					$batches.push($crate::BenchmarkBatch {
						results: $( $location )*::run_benchmark(
							benchmark,
							&lowest_range_values[..],
							&highest_range_values[..],
							&steps[..],
							repeat,
						)?,
						pallet: $name.to_vec(),
						benchmark: benchmark.to_vec(),
					});
				}
			} else {
				$batches.push($crate::BenchmarkBatch {
					results: $( $location )*::run_benchmark(
						&benchmark[..],
						&lowest_range_values[..],
						&highest_range_values[..],
						&steps[..],
						repeat,
					)?,
					pallet: $name.to_vec(),
					benchmark: benchmark.clone(),
				});
			}
		}
	)
}
