use super::*;

mod deprecated {
    use super::*;

    decl_module! {
        pub struct Module<T: Trait> for enum Call where origin: T::Origin { }
    }
    
    decl_storage! {
        trait Store for Module<T: Trait> as Session {
            pub NextKeys: double_map hasher(twox_64_concat) Vec<u8>, hasher(opaque_blake2_256) T::ValidatorId
                => Option<T::Keys>;
            pub KeyOwner: double_map hasher(twox_64_concat) Vec<u8>, hasher(opaque_blake2_256) (KeyTypeId, Vec<u8>)
                => Option<T::ValidatorId>;
        }
    }
}

const DEDUP_KEY_PREFIX: &[u8] = b":session:keys";

pub fn migrate_account<T: Trait>(a: &T::AccountId) {
    frame_support::runtime_print!("🕊️  Migrating Session Account '{:?}'", a);
    if let Some(v) = T::ValidatorIdOf::convert(a.clone()) {
        frame_support::runtime_print!("Validator Id '{:?}'", v);
        if let Some(keys) = deprecated::NextKeys::<T>::take(DEDUP_KEY_PREFIX, &v) {
            frame_support::runtime_print!("Keys '{:?}'", keys);
            NextKeys::<T>::insert(&v, &keys);
            for id in T::Keys::key_ids() {
                if let Some(owner) = deprecated::KeyOwner::<T>::take(DEDUP_KEY_PREFIX, (*id, keys.get_raw(*id))) {
                    frame_support::runtime_print!("Owner '{:?}'", owner);
                    KeyOwner::<T>::insert((*id, keys.get_raw(*id)), owner);
                }
            }
        }
    }
    frame_support::runtime_print!("🕊️  Done Session Account '{:?}'", a);
}
