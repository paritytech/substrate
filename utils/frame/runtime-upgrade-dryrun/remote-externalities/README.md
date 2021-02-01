# remote-externalities

## Remote Externalities

An equivalent of `sp_io::TestExternalities` that can load its state from a remote substrate
based chain.

##### Building

Building this crate can be bit tricky, here are some advise about it.

You have two main issues:

1. You need to get your hand on a `Runtime`; something that implements all of the pallet
   `Config` traits (formerly `trait Trait`).
2. If that runtime happens to come from the polkadot repo, you need to make sure it compiles.

In both cases, you probably also need to import an un-merged pallet from substrate that you are
working on, so let's first take a look at that.

You need to building such a structure:

```rust
.
| -- ./substrate (where you are coding something new that needs to be tested)
| -- ./substrate-debug-kit (your beloved debug kit)
```

From the sibling substrate, you probably want to import `./substrate/frame/new-pallet`. Then,
you need to make sure dependencies used by this crate (i.e. `sp-io`) match the ones being used
in `new-pallet` (otherwise there's a 99% chance that some dependency version resolution will
fail -- try it if you feel fancy). To do this, the easiest way is to make this repo's
dependencies point to your sibling substrate. You can use _cargo path override_ for this, but
there's also a simpler script for this. Simply run `node update_cargo.js local` in the root of
this repo and all of the substrate dependencies will point to a sibling substrate. Use `node
update_cargo.js exact` to switch back.

> At this point, if there has been a breaking change in `sp-*` crates, this crate might not
compile. Please make an issue. This is rather rare.

Now we can get to the above issues again. You have two opitions:

1. Build a mock runtime, similar how to you would build one in a pallet test (see example
   below). The very important point here is that this mock needs to hold real values for types
   that matter for you. Some typical ones are:

- `sp_runtime::AccountId32` as `AccountId`.
- `u32` as `BlockNumber`.
- `u128` as Balance.

And most importantly the types of `my-pallet`. Once you have your `Runtime`, you can use it for
storage type resolution and do things like `<my_pallet::Pallet<Runtime>>::funciton()` or
`<my_pallet::StorageItem<Runtime>>::get()`.

2. Finally, the second option:

If you you alredy have new pallet integrated in polkadot, you can directly pull
`polkadot-runtime` or `kusama-runtime` and use that, like `use polkadot_runtime::Runtime` (which
will take a week to compile). Note that you, again, have to make sure that the substrate
dependencies don't clash: You need a local polkadot repo next to the above two, use it to import
the `Runtime`, and make sure there is a `.cargo/config` file in polkadot overrding substrate
dependencies to point to the local one.

> I personally recommend building a mock runtime if you only use remote-externalities, and use a
real runtime if you ise `migration-dry-run`.

#### Example

With a test runtime

```rust
use remote_externalities::Builder;

#[derive(Clone, Eq, PartialEq, Debug, Default)]
pub struct TestRuntime;

use frame_system as system;
impl_outer_origin! {
    pub enum Origin for TestRuntime {}
}

impl frame_system::Config for TestRuntime {
    ..
    // we only care about these two for now. The rest can be mock. The block number type of
    // kusama is u32.
    type BlockNumber = u32;
    type Header = Header;
    ..
}

#[test]
fn test_runtime_works() {
    let hash: Hash =
        hex!["f9a4ce984129569f63edc01b1c13374779f9384f1befd39931ffdcc83acf63a7"].into();
    let parent: Hash =
        hex!["540922e96a8fcaf945ed23c6f09c3e189bd88504ec945cc2171deaebeaf2f37e"].into();
    Builder::new()
        .at(hash)
        .module("System")
        .build()
        .execute_with(|| {
            assert_eq!(
                // note: the hash corresponds to 3098546. We can check only the parent.
                // https://polkascan.io/kusama/block/3098546
                <frame_system::Module<Runtime>>::block_hash(3098545u32),
                parent,
            )
        });
}
```

Or with the real kusama runtime.

```rust
use remote_externalities::Builder;
use kusama_runtime::Runtime;

#[test]
fn test_runtime_works() {
    let hash: Hash =
        hex!["f9a4ce984129569f63edc01b1c13374779f9384f1befd39931ffdcc83acf63a7"].into();
    Builder::new()
        .at(hash)
        .module("Staking")
        .build()
        .execute_with(|| assert_eq!(<pallet_staking::Module<Runtime>>::validator_count(), 400));
}
