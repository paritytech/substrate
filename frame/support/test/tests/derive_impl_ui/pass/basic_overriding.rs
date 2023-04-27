use frame_support::*;
use static_assertions::assert_type_eq_all;

pub trait Animal {
	type Locomotion;
	type Diet;
	type SleepingStrategy;
	type Environment;

	fn animal_name() -> &'static str;
}

pub type RunsOnFourLegs = (usize, usize, usize, usize);
pub type RunsOnTwoLegs = (usize, usize);
pub type Swims = isize;
pub type Diurnal = bool;
pub type Omnivore = char;
pub type Land = ((), ());
pub type Sea = ((), (), ());

pub struct FourLeggedAnimal {}

#[register_default_impl(FourLeggedAnimal)]
impl Animal for FourLeggedAnimal {
	type Locomotion = RunsOnFourLegs;
	type Diet = Omnivore;
	type SleepingStrategy = Diurnal;
	type Environment = Land;

	fn animal_name() -> &'static str {
		"A Four-Legged Animal"
	}
}

pub struct AcquaticMammal {}

#[derive_impl(FourLeggedAnimal, Animal)]
impl Animal for AcquaticMammal {
	type Locomotion = (Swims, RunsOnFourLegs);
	type Environment = (Land, Sea);
}

assert_type_eq_all!(<AcquaticMammal as Animal>::Locomotion, (Swims, RunsOnFourLegs));
assert_type_eq_all!(<AcquaticMammal as Animal>::Environment, (Land, Sea));
assert_type_eq_all!(<AcquaticMammal as Animal>::Diet, Omnivore);
assert_type_eq_all!(<AcquaticMammal as Animal>::SleepingStrategy, Diurnal);

fn main() {}
