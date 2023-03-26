# Changelog

All notable changes to this project will be documented in this file.

The format is loosely based
on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/). We maintain a
single integer version number for staking pallet to keep track of all storage
migrations.

## [v14]

### Added

- New item `ErasStakersPaged` that keeps up to `MaxExposurePageSize`
  individual nominator exposures by era, validator and page.
- New item `ErasStakersOverview` complementary to `ErasStakersPaged` which keeps
  state of own and total stake of the validator across pages.
- New item `ClaimedRewards` to support paged rewards payout.

### Deprecated

- `ErasStakersClipped` is deprecated and may be removed after 84 eras.
- `ErasStakers` is deprecated and may be removed after 84 eras.
- Field `claimed_rewards` in item `Ledger` is renamed
  to `legacy_claimed_rewards` and may be removed after 84 eras.

[v14]: https://github.com/paritytech/substrate/pull/13498
