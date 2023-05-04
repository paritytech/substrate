use frame_support::*;

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
pub type Nocturnal = Option<bool>;
pub type Omnivore = char;
pub type Land = ((), ());
pub type Sea = ((), (), ());
pub type Carnivore = (char, char);

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

// Should throw: `error: cannot find macro `__export_tokens_tt_tiger` in this scope`
//
// Note that there is really no better way to clean up this error, tt_call suffers from the
// same downside but this is really the only rough edge when using macro magic.
#[derive_impl(Tiger as Animal)]
impl Animal for AcquaticMammal {
	type Locomotion = (Swims, RunsOnFourLegs);
	type Environment = (Land, Sea);
}

fn main() {}
