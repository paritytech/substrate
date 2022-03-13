#![allow(clippy::too_many_arguments)]
use super::*;

/// Trait to handle asset locking mechanism to ensure interactions with the asset can be implemented
/// downstream to extend logic of Uniques current functionality
#[allow(clippy::upper_case_acronyms)]
pub trait Locker<ClassId, InstanceId> {
    /// Check if the asset should be locked and prevent interactions with the asset from executing.
    /// Default will be false if not implemented downstream
    fn check_should_lock(class: ClassId, instance: InstanceId) -> bool;
}

impl<ClassId, InstanceId> Locker<ClassId, InstanceId> for () {
    fn check_should_lock(_class: ClassId, _instance: InstanceId) -> bool {
        false
    }
}

impl<T: Config<I>, I: 'static> Locker<T::ClassId, T::InstanceId> for Pallet<T, I> {
    fn check_should_lock(_class: T::ClassId, _instance: T::InstanceId) -> bool {
        false
    }
}
