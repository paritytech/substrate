## `Polkadot` projects is a **OPENISH Open Source Project**
-----------------------------------------

## What?

Individuals making significant and valuable contributions are given commit-access to a project to contribute as they see fit. A project is more like an open wiki than a standard guarded open source project.

## Rules

There are a few basic ground-rules for contributors (including the maintainer(s) of the project):

1. **No `--force` pushes** or modifying the Git history in any way. If you need to rebase, ensure you do it in your own repo.
1. **Non-master branches**, prefixed with a short name moniker (e.g. `gav-my-feature`) must be used for ongoing work.
1. **All modifications** must be made in a **pull-request** to solicit feedback from other contributors.
1. A pull-request *must not be merged until CI* has finished successfully.
1. Contributors should adhere to the [house coding style](https://github.com/paritytech/polkadot/wiki/Style-Guide).

Merging pull requests once CI is successful:

1. A pull request that does not alter any logic (e.g. comments, dependencies, docs) may be tagged [`insubstantial`](https://github.com/paritytech/polkadot/pulls?utf8=%E2%9C%93&q=is%3Apr+is%3Aopen+label%3AA2-insubstantial+) and merged by its author.
1. A pull request with no large change to logic that is an urgent fix may be merged after a non-author contributor has reviewed it well.
1. All other PRs should sit for 48 hours with the [`pleasereview`](https://github.com/paritytech/polkadot/pulls?q=is%3Apr+is%3Aopen+label%3AA0-pleasereview) tag in order to garner feedback.
1. No PR should be merged until all reviews' comments are addressed.

Reviewing pull requests:

When reviewing a pull request, the end-goal is to suggest useful changes to the author. Reviews should finish with approval unless there are issues that would result in:

1. Buggy behaviour.
1. Undue maintenance burden.
1. Breaking with house coding style.
1. Pessimisation (i.e. reduction of speed as measured in the projects benchmarks).
1. Feature reduction (i.e. it removes some aspect of functionality that a significant minority of users rely on).
1. Uselessness (i.e. it does not strictly add a feature or fix a known issue).

Reviews may not be used as an effective veto for a PR because:

1. There exists a somewhat cleaner/better/faster way of accomplishing the same feature/fix.
1. It does not fit well with some other contributors' longer-term vision for the project.

## Releases

Declaring formal releases remains the prerogative of the project maintainer(s).

## Changes to this arrangement

This is an experiment and feedback is welcome! This document may also be subject to pull-requests or changes by contributors where you believe you have something valuable to add or change.

## Heritage

These contributing guidelines are modified from the "OPEN Open Source Project" guidelines for the Level project: https://github.com/Level/community/blob/master/CONTRIBUTING.md

-----------------------------------------
