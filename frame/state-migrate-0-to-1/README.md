# State migration pallet v0 to v1

One shot migration from `StateVersion::V0` to `StateVersion::V1`.

Module need to be included to force lazy state update on all values.
Can be remove when `StateProgress` becomes `Finished`.
