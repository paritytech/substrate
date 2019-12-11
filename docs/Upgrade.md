# Upgrade path for you building on substrate

## master
 - crate rename has been fixed `sp-application-crypto` (was `sc-application-crypto`);  `.maintain/rename-crates-for-2.0.sh` has been updated accordingly, you can use it to upgrade to latest naming convention
 - crates have been renamed, run `bash .maintain/rename-crates-for-2.0.sh`