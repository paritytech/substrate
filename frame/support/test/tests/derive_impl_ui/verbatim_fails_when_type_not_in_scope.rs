use frame_support::{*, pallet_macros::verbatim};
use static_assertions::assert_type_eq_all;

pub trait Shape {
    type Area;
}

struct DefaultShape;

#[register_default_impl(DefaultShape)]
impl Shape for DefaultShape {
    #[verbatim]
    type Area = ();
}

struct Circle;

#[derive_impl(DefaultShape)] // Injects type Area = Area;
impl Shape for Circle {}

assert_type_eq_all!(<Circle as Shape>::Area, ());

fn main() {}
