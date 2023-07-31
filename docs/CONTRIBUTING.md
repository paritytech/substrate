# Contributing

The `Substrate` project is an ***OPENISH Open Source Project***

Contributors are invited to our `#frame-contributors` channel on the Polkadot Discord for support and coordination:  
[![Discord](https://img.shields.io/discord/722223075629727774?style=for-the-badge&logo=discord&label=Discord)](https://dot.li/discord)

## What?

Individuals making significant and valuable contributions are given commit-access to a project to contribute as they see fit. A project is more like an open wiki than a standard guarded open source project.

## Rules

There are a few basic ground-rules for contributors (including the maintainer(s) of the project):

1. ***No `--force` pushes*** or modifying the master branch history in any way. If you need to rebase, ensure you do it in your own repo. No rewriting of the history after the code has been shared (e.g. through a Pull-Request).
2. ***Non-master branches***, prefixed with a short name moniker (e.g. `gav-my-feature`) must be used for ongoing work.
3. ***All modifications*** must be made in a ***pull-request*** to solicit feedback from other contributors.
4. A pull-request **must not be merged until CI** has finished successfully.
5. Contributors should adhere to the [house coding style](STYLE_GUIDE.md).
6. Contributors should adhere to the [house documenting style](DOCUMENTATION_GUIDELINES.md), when applicable.

## Merge Process

**In General**

A Pull Request (PR) needs to be reviewed and approved by project maintainers unless:

* it does not alter any logic (e.g. comments, dependencies, docs), then it may be tagged [`insubstantial`](https://github.com/paritytech/substrate/pulls?utf8=%E2%9C%93&q=is%3Apr+is%3Aopen+label%3AA2-insubstantial) and merged by its author once CI is complete.
* it is an urgent fix with no large change to logic, then it may be merged after a non-author contributor has approved the review once CI is complete.

**Labels TLDR:**

* `A-*` Pull request status. ONE REQUIRED.
* `B-*` Changelog and/or Runtime-upgrade post composition markers. ONE REQUIRED. (used by automation)
* `C-*` Release notes release-criticality markers. EXACTLY ONE REQUIRED. (used by automation)
* `D-*` Audit tags denoting auditing requirements on the PR.

**Process:**

1. Please tag each PR with exactly one `A`, `B`, `C` and `D` label at the minimum.
2. When tagging a PR, it should be done while keeping all downstream users in mind. Downstream users are not just Polkadot or system parachains, but also all the other parachains and solo chains that are using Substrate. The labels are used by downstream users to track changes and to include these changes properly into their own releases.
3. Once a PR is ready for review please add the [`A0-please_review`](https://github.com/paritytech/substrate/pulls?q=is%3Apr+is%3Aopen+label%3AA0-please_review+) label. Generally PRs should sit with this label for 48 hours in order to garner feedback. It may be merged before if all relevant parties had a look at it.
4. If the first review is not an approval, swap `A0-please_review` to any label `[A3, A5]` to indicate that the PR has received some feedback, but needs further work. For example. [`A3-in_progress`](https://github.com/paritytech/substrate/labels/A3-in_progress) is a general indicator that the PR is work in progress.
5. PRs must be tagged with `B*` labels to signal if a change is note worthy for downstream users. The respective `T*` labels should be added to signal the component that was changed. `B0-silent` must only be used for changes that don’t require any attention by downstream users.
6. PRs must be tagged with their release importance via the `C1-C7` labels. The release importance is only informing about how important it is to apply a release that contains the change.
7. PRs must be tagged with their audit requirements via the `D1-D9` labels.
8. PRs that introduce runtime migrations must be tagged with [`E0-runtime_migration`](https://github.com/paritytech/substrate/labels/E0-runtime_migration). See the [Migration Best Practices here](https://github.com/paritytech/substrate/blob/master/utils/frame/try-runtime/cli/src/lib.rs#L18) for more info about how to test runtime migrations.
9. PRs that introduce irreversible database migrations must be tagged with [`E1-database_migration`](https://github.com/paritytech/substrate/labels/E1-database_migration).
10. PRs that add host functions must be tagged with with [`E3-host_functions`](https://github.com/paritytech/substrate/labels/E3-host_functions).
11. PRs that break the external API must be tagged with [`F3-breaks_API`](https://github.com/paritytech/substrate/labels/F3-breaks_API).
12. PRs that change the mechanism for block authoring in a backwards-incompatible way must be tagged with [`F1-breaks_authoring`](https://github.com/paritytech/substrate/labels/F1-breaks_authoring).
13. PRs that "break everything" must be tagged with [`F0-breaks_everything`](https://github.com/paritytech/substrate/labels/F0-breaks_everything).
14. PRs should be categorized into projects.
15. No PR should be merged until all reviews' comments are addressed and CI is successful.

**Noting relevant changes:**

When breaking APIs, it should be mentioned on what was changed in the PR description alongside some examples on how to change the code to make it work/compile.

The PR description should also mention potential storage migrations and if they require some special setup aside adding it to the list of migrations in the runtime.

**Reviewing pull requests:**

When reviewing a pull request, the end-goal is to suggest useful changes to the author. Reviews should finish with approval unless there are issues that would result in:

1. Buggy behavior.
2. Undue maintenance burden.
3. Breaking with house coding style.
4. Pessimization (i.e. reduction of speed as measured in the projects benchmarks).
5. Feature reduction (i.e. it removes some aspect of functionality that a significant minority of users rely on).
6. Uselessness (i.e. it does not strictly add a feature or fix a known issue).

**Reviews may not be used as an effective veto for a PR because**:

1. There exists a somewhat cleaner/better/faster way of accomplishing the same feature/fix.
2. It does not fit well with some other contributors' longer-term vision for the project.

### Updating Polkadot as well

***All pull requests will be checked against either Polkadot master, or your provided Polkadot companion PR***. That is, If your PR changes the external APIs or interfaces used by Polkadot. If you tagged the PR with `breaksapi` or `breaksconsensus` this is most certainly the case, in all other cases check for it by running step 1 below.

To create a Polkadot companion PR:

1. Pull latest Polkadot master (or clone it, if you haven’t yet).
2. Override substrate deps to point to your local path or branch using https://github.com/bkchr/diener. (E.g. from the Polkadot clone dir run `diener patch --crates-to-patch ../substrate --substrate` assuming substrate clone is in a sibling dir. If you do use diener, ensure that you _do not_ commit the changes diener makes to the Cargo.tomls.)
3. Make the changes required and build Polkadot locally.
4. Submit all this as a PR against the Polkadot Repo.
5. In the _description_ of your _Substrate_ PR add "Polkadot companion: [Polkadot_PR_URL]"
6. Now you should see that the `check_polkadot` CI job will build your Substrate PR against the mentioned Polkadot branch in your PR description.
7. Someone will need to approve the Polkadot PR before the Substrate CI will go green. (The Polkadot CI failing can be ignored as long as the Polkadot job in the _substrate_ PR is green).
8. Wait for reviews on both the Substrate and the Polkadot PRs.
9. Once the Substrate PR runs green, a member of the `parity` Github group can comment on the Substrate PR with `bot merge` which will:
   * Merge the Substrate PR.
   * The bot will push a commit to the Polkadot PR updating its Substrate reference. (effectively doing `cargo update -p sp-io`)
   * If the Polkadot PR origins from a fork then a project member may need to press `approve run` on the Polkadot PR.
   * The bot will merge the Polkadot PR once all its CI `{"build_allow_failure":false}` checks are green.
       Note: The merge-bot currently doesn’t work with forks on org accounts, only individual accounts.
   	(Hint: it’s recommended to use `bot merge` to merge all substrate PRs, not just ones with a Polkadot companion.)

If your PR is reviewed well, but a Polkadot PR is missing, signal it with [`E6-needs_polkadot_pr`](https://github.com/paritytech/substrate/labels/E6-needs_polkadot_pr) to prevent it from getting automatically merged. In most cases the CI will add this label automatically.

As there might be multiple pending PRs that might conflict with one another, a) you should not merge the substrate PR until the Polkadot PR has also been reviewed and b) both should be merged pretty quickly after another to not block others.

## Helping out

We use [labels](https://paritytech.github.io/labels/doc_substrate.html) to manage PRs and issues and communicate state of a PR. Please familiarize yourself with them. The best way to get started is to a pick a ticket tagged [`easy`](https://github.com/paritytech/substrate/issues?q=is%3Aissue+is%3Aopen+label%3AZ1-easy) or [`medium`](https://github.com/paritytech/substrate/issues?q=is%3Aissue+is%3Aopen+label%3AZ2-medium) and get going or [`mentor`](https://github.com/paritytech/substrate/issues?q=is%3Aissue+is%3Aopen+label%3AZ6-mentor) and get in contact with the mentor offering their support on that larger task.

## Issues
Please label issues with the following labels:

1. `I-**` or `J-**` Issue severity and type. EXACTLY ONE REQUIRED.
2. `U-*` Issue urgency, suggesting in what time manner does this issue need to be resolved. AT MOST ONE ALLOWED.
3. `Z-*` Issue difficulty. AT MOST ONE ALLOWED.

## Releases

Declaring formal releases remains the prerogative of the project maintainer(s).

## UI tests

UI tests are used for macros to ensure that the output of a macro doesn’t change and is in the expected format. These UI tests are sensible to any changes
in the macro generated code or to switching the rust stable version. The tests are only run when the `RUN_UI_TESTS` environment variable is set. So, when
the CI is for example complaining about failing UI tests and it is expected that they fail these tests need to be executed locally. To simplify the updating
of the UI test output there is the `.maintain/update-rust-stable.sh` script. This can be run with `.maintain/update-rust-stable.sh CURRENT_STABLE_VERSION`
and then it will run all UI tests to update the expected output.

## Changes to this arrangement

This is an experiment and feedback is welcome! This document may also be subject to pull-requests or changes by contributors where you believe you have something valuable to add or change.

## Heritage

These contributing guidelines are modified from the "OPEN Open Source Project" guidelines for the Level project: https://github.com/Level/community/blob/master/CONTRIBUTING.md
