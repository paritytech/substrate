use frame_support::{*, pallet_macros::verbatim};
use static_assertions::assert_type_eq_all;

pub trait Shape {
    type Area;
}

type Area = f32;

struct DefaultShape;

#[register_default_impl(DefaultShape)]
impl Shape for DefaultShape {
    #[verbatim]
    type Area = Area;
}

struct Circle;

#[derive_impl(DefaultShape)] // Injects type Area = Area;
impl Shape for Circle {}

assert_type_eq_all!(<Circle as Shape>::Area, Area);

fn main() {}
