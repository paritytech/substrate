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

mod utils;
pub use utils::*;

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
///   _ {
///     let l in 1 .. MAX_LENGTH => initialize_l(l);
///   }
///
///   // first dispatchable: foo; this is a user dispatchable and operates on a `u8` vector of
///   // size `l`, which we allow to be initialised as usual.
///   foo {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let l = ...;
///   } _(Origin::Signed(caller), vec![0u8; l])
///
///   // second dispatchable: bar; this is a root dispatchable and accepts a `u8` vector of size
///   // `l`. We don't want it preininitialised like before so we override using the `=> ()`
///   // notation.
///   // In this case, we explicitly name the call using `bar` instead of `_`.
///   bar {
///     let l = _ .. _ => ();
///   } bar(Origin::Root, vec![0u8; l])
///
///   // third dispatchable: baz; this is a user dispatchable. It isn't dependent on length like the
///   // other two but has its own complexity `c` that needs setting up. It uses `caller` (in the
///   // pre-instancing block) within the code block. This is only allowed in the param instancers
///   // of arms. Instancers of common params cannot optimistically draw upon hypothetical variables
///   // that the arm's pre-instancing code block might have declared.
///   baz1 {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let c = 0 .. 10 => setup_c(&caller, c);
///   } baz(Origin::Signed(caller))
///
///   // this is a second benchmark of the baz dispatchable with a different setup.
///   baz2 {
///     let caller = account::<T>(b"caller", 0, benchmarks_seed);
///     let c = 0 .. 10 => setup_c_in_some_other_way(&caller, c);
///   } baz(Origin::Signed(caller))
///
///   // this is benchmarking some code that is not a dispatchable.
///   populate_a_set {
///     let x in 0 .. 10_000;
///     let mut m = Vec::<u32>::new();
///     for i in 0..x {
///       m.insert(i);
///     }
///   } { m.into_iter().collect::<BTreeSet>() }
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
		$crate::benchmarks_iter!({
			$( { $common , $common_from , $common_to , $common_instancer } )*
		} ( ) $( $rest )* );
	}
}

#[macro_export]
macro_rules! impl_benchmark {
	(
		$( $name:ident ),*
	) => {
		impl<T: Trait> $crate::Benchmarking<$crate::BenchmarkResults> for Module<T> {
			fn run_benchmark(extrinsic: Vec<u8>, steps: u32, repeat: u32) -> Result<Vec<$crate::BenchmarkResults>, &'static str> {
				// Map the input to the selected benchmark.
				let extrinsic = sp_std::str::from_utf8(extrinsic.as_slice())
					.map_err(|_| "Could not find extrinsic")?;
				let selected_benchmark = match extrinsic {
					$( stringify!($name) => SelectedBenchmark::$name, )*
					_ => return Err("Could not find extrinsic."),
				};

				// Warm up the DB
				$crate::benchmarking::commit_db();
				$crate::benchmarking::wipe_db();

				// first one is set_identity.
				let components = <SelectedBenchmark as $crate::BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::components(&selected_benchmark);
				// results go here
				let mut results: Vec<$crate::BenchmarkResults> = Vec::new();
				// Select the component we will be benchmarking. Each component will be benchmarked.
				for (name, low, high) in components.iter() {
					// Create up to `STEPS` steps for that component between high and low.
					let step_size = ((high - low) / steps).max(1);
					let num_of_steps = (high - low) / step_size;
					for s in 0..num_of_steps {
						// This is the value we will be testing for component `name`
						let component_value = low + step_size * s;

						// Select the mid value for all the other components.
						let c: Vec<($crate::BenchmarkParameter, u32)> = components.iter()
							.map(|(n, l, h)|
								(*n, if n == name { component_value } else { (h - l) / 2 + l })
							).collect();

						// Run the benchmark `repeat` times.
						for _ in 0..repeat {
							// Set up the externalities environment for the setup we want to benchmark.
							let (call, caller) = <SelectedBenchmark as $crate::BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>>>::instance(&selected_benchmark, &c)?;
							// Commit the externalities to the database, flushing the DB cache.
							// This will enable worst case scenario for reading from the database.
							$crate::benchmarking::commit_db();
							// Run the benchmark.
							let start = $crate::benchmarking::current_time();
							call.dispatch(caller.into())?;
							let finish = $crate::benchmarking::current_time();
							let elapsed = finish - start;
							results.push((c.clone(), elapsed));
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

#[macro_export]
#[allow(missing_docs)]
macro_rules! benchmarks_iter {
	// mutation arm:
	(
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: _ ( $origin:expr $( , $arg:expr )* )
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			{ $( $common )* } ( $( $names )* ) $name { $( $code )* }: $name ( $origin $( , $arg )* ) $( $rest )*
		}
	};
	// mutation arm:
	(
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: $dispatch:ident ( $origin:expr $( , $arg:expr )* )
		$( $rest:tt )*
	) => {
		$crate::benchmarks_iter! {
			{ $( $common )* } ( $( $names )* ) $name { $( $code )* }: { Ok((crate::Call::<T>::$dispatch($($arg),*), $origin)) } $( $rest )*
		}
	};
	// iteration arm:
	(
		{ $( $common:tt )* }
		( $( $names:ident )* )
		$name:ident { $( $code:tt )* }: { $eval:expr }
		$( $rest:tt )*
	) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } { } { $eval } { $( $code )* }
		}
		$crate::benchmarks_iter!( { $( $common )* } ( $( $names )* $name ) $( $rest )* );
	};
	// iteration-exit arm
	( { $( $common:tt )* } ( $( $names:ident )* ) ) => {
		$crate::selected_benchmark!( $( $names ),* );
		$crate::impl_benchmark!( $( $names ),* );
	}
}

#[macro_export]
#[allow(missing_docs)]
macro_rules! benchmark_backend {
	// parsing arms
	($name:ident {
		$( $common:tt )*
	} {
		$( PRE { $( $pre_parsed:tt )* } )*
	} { $eval:expr } {
			let $pre_id:tt : $pre_ty:ty = $pre_ex:expr;
			$( $rest:tt )*
	} ) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } {
				$( PRE { $( $pre_parsed )* } )*
				PRE { $pre_id , $pre_ty , $pre_ex }
			} { $eval } { $( $rest )* }
		}
	};
	($name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $param:ident in ( $param_from:expr ) .. $param_to:expr => $param_instancer:expr;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } {
				$( $parsed )*
				PARAM { $param , $param_from , $param_to , $param_instancer }
			} { $eval } { $( $rest )* }
		}
	};
	// mutation arm to look after defaulting to a common param
	($name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $param:ident in ...;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name {
				$( { $common , $common_from , $common_to , $common_instancer } )*
			} {
				$( $parsed )*
			} { $eval } {
				let $param
					in ({ $( let $common = $common_from; )* $param })
					.. ({ $( let $common = $common_to; )* $param })
					=> ({ $( let $common = || -> Result<(), &'static str> { $common_instancer ; Ok(()) }; )* $param()? });
				$( $rest )*
			}
		}
	};
	// mutation arm to look after defaulting only the range to common param
	($name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $param:ident in _ .. _ => $param_instancer:expr ;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name {
				$( { $common , $common_from , $common_to , $common_instancer } )*
			} {
				$( $parsed )*
			} { $eval } {
				let $param
					in ({ $( let $common = $common_from; )* $param })
					.. ({ $( let $common = $common_to; )* $param })
					=> $param_instancer ;
				$( $rest )*
			}
		}
	};
	// mutation arm to look after a single tt for param_from.
	($name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $param:ident in $param_from:tt .. $param_to:expr => $param_instancer:expr ;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } { $( $parsed )* } { $eval } {
				let $param in ( $param_from ) .. $param_to => $param_instancer;
				$( $rest )*
			}
		}
	};
	// mutation arm to look after the default tail of `=> ()`
	($name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $param:ident in $param_from:tt .. $param_to:expr;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } { $( $parsed )* } { $eval } {
				let $param in $param_from .. $param_to => ();
				$( $rest )*
			}
		}
	};
	// mutation arm to look after `let _ =`
	($name:ident {
		$( $common:tt )*
	} {
		$( $parsed:tt )*
	} { $eval:expr } {
		let $pre_id:tt = $pre_ex:expr;
		$( $rest:tt )*
	}) => {
		$crate::benchmark_backend! {
			$name { $( $common )* } { $( $parsed )* } { $eval } {
				let $pre_id : _ = $pre_ex;
				$( $rest )*
			}
		}
	};
	// actioning arm
	($name:ident {
		$( { $common:ident , $common_from:tt , $common_to:expr , $common_instancer:expr } )*
	} {
		$( PRE { $pre_id:tt , $pre_ty:ty , $pre_ex:expr } )*
		$( PARAM { $param:ident , $param_from:expr , $param_to:expr , $param_instancer:expr } )*
	} { $eval:expr } { $( $post:tt )* } ) => {
		#[allow(non_camel_case_types)]
		struct $name;
		#[allow(unused_variables)]
		impl<T: Trait> $crate::BenchmarkingSetup<T, crate::Call<T>, RawOrigin<T::AccountId>> for $name {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				vec! [
					$(
						($crate::BenchmarkParameter::$param, $param_from, $param_to)
					),*
				]
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<(crate::Call<T>, RawOrigin<T::AccountId>), &'static str>
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
				$eval
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
		$( $bench:ident ),*
	) => {
		// The list of available benchmarks for this pallet.
		#[allow(non_camel_case_types)]
		enum SelectedBenchmark {
			$( $bench, )*
		}

		// Allow us to select a benchmark from the list of available benchmarks.
		impl<T: Trait> $crate::BenchmarkingSetup<T, Call<T>, RawOrigin<T::AccountId>> for SelectedBenchmark {
			fn components(&self) -> Vec<($crate::BenchmarkParameter, u32, u32)> {
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<
						T,
						Call<T>,
						RawOrigin<T::AccountId>,
					>>::components(&$bench), )*
				}
			}

			fn instance(&self, components: &[($crate::BenchmarkParameter, u32)])
				-> Result<(Call<T>, RawOrigin<T::AccountId>), &'static str>
			{
				match self {
					$( Self::$bench => <$bench as $crate::BenchmarkingSetup<
						T,
						Call<T>,
						RawOrigin<T::AccountId>,
					>>::instance(&$bench, components), )*
				}
			}
		}
	};
}
