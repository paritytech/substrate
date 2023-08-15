# Changelog

All notable changes to this pallet will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this pallet adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

The semantic versioning guarantees cover the interface to the substrate runtime which
includes this pallet as a dependency. This module will also add storage migrations whenever
changes require it. Stability with regard to offchain tooling is explicitly excluded from
this guarantee: For example adding a new field to an in-storage data structure will require
changes to frontends to properly display it. However, those changes will still be regarded
as a minor version bump.

## [Unreleased]

### Added

-  Introduce `Payees` and `PayoutDestination` with `Split` variant, which starts a lazy migration to move existing `Payee` items to a new `Payees` storage item.
[#14451](https://github.com/paritytech/substrate/pull/14451)