# Substrate Documentation Guidelines

This document is only focused on documenting parts of substrate that relates to its external API. The list of such crates can be found in [CODEOWNERS](./CODEOWNERS). Search for the crates that are auto-assigned to a team called `docs-audit`.

These are crates that are often used by external developers and need more thorough documentation. These are the crates most concerned with FRAME development.

- [Substrate Documentation Guidelines](#substrate-documentation-guidelines)
  - [General/Non-Pallet Crates](#generalnon-pallet-crates)
    - [What to Document?](#what-to-document)
      - [Rust Docs vs. Code Comments](#rust-docs-vs-code-comments)
    - [How to Document?](#how-to-document)
    - [TLDR](#tldr)
    - [Other Guidelines](#other-guidelines)
      - [Document Through Code](#document-through-code)
      - [Formatting Matters](#formatting-matters)
  - [Pallet Crates](#pallet-crates)
    - [Top Level Pallet Docs (`lib.rs`)](#top-level-pallet-docs-librs)
    - [Dispatchable](#dispatchable)
    - [Storage Items](#storage-items)


## General/Non-Pallet Crates

First, consider the case for all such crates, except for those that are pallets.

### What to Document?

The first question is, what should you document? Use the following filter:

1. Within the set of crates above,
2. All `pub` item within the aforementioned crates need to be documented. If it is not `pub`, it does not appear in the rust-docs, and is not public facing.
    * Within `pub` items, sometimes they are only `pub` in order to be used by another internal crate, and you can foresee that this will not be used by anyone else other than you. These need **not** be documented thoroughly, and are left to your discretion to identify.
    * Reminder: `trait` items are public by definition, if the trait is public.
3. All public modules (`mod`) should have reasonable module-level documentation (`//!`).


#### Rust Docs vs. Code Comments

Note that anything starting with `///` is an external rust-doc, and everything starting with `//` does not appear in the rust-docs. It's important to not confuse the two in your documentation.

```rust
/// Computes the square root of the input, returning `Ok(_)` if successful.
///
/// # Errors
/// ...
///
// Details about the complexity, how you implemented this, and some quirks that
// are NOT relevant to the external interface, so it starts with '//'.
// This can also be moved inside the function.
pub fn sqrt(x: u32) -> Result<u32, ()> {
    todo!();
}

```

### How to Document?

There are a few very good sources that you can look into:

- https://doc.rust-lang.org/rustdoc/how-to-write-documentation.html
- https://web.mit.edu/rust-lang_v1.25/arch/amd64_ubuntu1404/share/doc/rust/html/book/first-edition/documentation.html
- https://blog.guillaume-gomez.fr/articles/2020-03-12+Guide+on+how+to+write+documentation+for+a+Rust+crate


As mentioned [here](https://web.mit.edu/rust-lang_v1.25/arch/amd64_ubuntu1404/share/doc/rust/html/book/first-edition/documentation.html#writing-documentation-comments) and [here](https://blog.guillaume-gomez.fr/articles/2020-03-12+Guide+on+how+to+write+documentation+for+a+Rust+crate), always start with a **single sentence** demonstrating what is being documented. All additional documentation should be added *after a newline*. Strive to make the first sentence succinct and short. The reason for this is the first paragraph of docs about an item (everything before the first newline) is used as the excerpt that rust doc displays about this item when it appears in tables, such as the table listing all functions in a module. If this excerpt is too long, the module docs will be very difficult to read.

About [special sections](https://web.mit.edu/rust-lang_v1.25/arch/amd64_ubuntu1404/share/doc/rust/html/book/first-edition/documentation.html#special-sections), we will most likely not need to think about panic and safety in any runtime related code. Our code is never `unsafe`, and will (almost) never panic.

Use `# Examples as much as possible. These are great ways to further demonstrate what your APIs are doing, and add free test coverage. As an additional benefit, any code in rust-docs is treated as an "integration tests", not unit tests, which tests your crate in a different way than unit tests. So, it is both a win for "more documentation" and a win for "more test coverage".

You can also consider having an `# Error` section optionally. Of course, this only applies if there is a `Result` being returned, and if the `Error` variants are overly complicated.

Strive to include correct links to other items in your written docs as much as possible. In other words, avoid \`some_func\` and instead use \[\`some_fund\`\]. Read more about how to correctly use links in your rust-docs [here](https://doc.rust-lang.org/rustdoc/write-documentation/linking-to-items-by-name.html#valid-links) and [here](https://rust-lang.github.io/rfcs/1946-intra-rustdoc-links.html#additions-to-the-documentation-syntax).

> While you are linking, you might become conscious of the fact that you are in need of linking to (too many) foreign items in order to explain your API. This is leaning more towards API-Design rather than documentation, but it is a warning that the subject API might be slightly wrong. For example, most "glue" traits[^1] in `frame/support` should be designed and documented without making hard assumptions about particular pallets that implement them.

### TLDR

0. Have the goal of enforcing `#![deny(missing_docs)]` mentally, even if it is not enforced by the compiler 🙈.
1. Start with a single, clear and concise sentence. Follow up with more context, after a newline, if needed.
2. Use examples as much as reasonably possible.
3. Use links as much as possible.
4. Think about context. If you are in need of explaining a lot of foreign topics in documenting a trait that should not explicitly depend on them, you have likely not designed it properly.


### Other Guidelines

The above five guidelines must always be reasonably respected in the documentation.

The following are a set of notes that may not necessarily hold in all circumstances:


#### Document Through Code

You should make sure that your code is properly-named and well-organized so that your code functions as a form of documentation. However, within the complexity of our projects in Polkadot/Substrate that is not enough. Particularly, things like examples, errors and panics cannot be documented only through properly-named and well-organized code.

> Our north star is self-documenting code that also happens to be well-documented and littered with examples.

* This is hard to scale at a project the size of Polkadot/Substrate. Moreover, things like examples, errors and panics cannot be documented via just code.

* Your written documents should *complement* the code, not *repeat* it. Put bluntly, if you end up writing this, you are likely doing it wrong:

 ```rust
 /// Sends request and handles the response.
 trait SendRequestAndHandleResponse {

 }
 ```

 Because the document is adding no extra information and you are better of without it.


#### Formatting Matters

The way you format your documents (newlines, heading and so on) do matter! Consider the below examples:

```rust
/// This function works with input u32 x and multiplies it by two. If
/// we optimize the other variant of it, we would be able to achieve more
/// efficiency but I have to think about it. Probably can panic if the input
/// overflows u32.
fn multiply_by_2(x: u32) -> u32 { .. }
```

```rust
/// Multiplies an input of type [`u32`] by two.
///
/// # Panics
///
/// Panics if the input overflows.
///
/// # Complexity
///
/// Is implemented using some algorithm that yields complexity of O(1).
// More efficiency can be achieved if we improve this via such and such.
fn multiply_by_2(x: u32) -> u32 { .. }
```

They are both roughly conveying the same set of facts, but one is substantially kinder on the eye. Especially for traits and type that you can foresee will be seen/used a lot, try and write the better version!

Similarly, make sure your comments are wrapped at 100 characters line-width (as defined by our [`rustfmt.toml`](../rustfmt.toml)), no **more and no less**! The more is fixed by `rustfmt` and our CI, but if you (some some unknown reason) wrap your lines at 59 characters, it will pass the CI, and it will not look good 🫣.

[^1]: Those that help two pallets talk to each other.

## Pallet Crates

Everything above is related to non-pallet details. They might be relevant in both crates that are pallets, and non-pallet crates.

The following is relevant to how to document parts of a crate that is a pallet.

### Top Level Pallet Docs (`lib.rs`)

For the top-level pallet docs, consider the following template:

```
//! # <Pallet Name>
//!
//! <single-liner about the pallet>.
//!
//! ## High-Level/End-User Details
//!
//! <a few paragraphs, focus on what external folks should know about the pallet>
//!
//! <The audience here is potentially non-coders who just want to know what this pallet does, not how it does it>
//!
//! ### Example
//!
//! <Your pallet must have a few tests that cover important user journeys. Use https://crates.io/crates/docify to reuse your these as examples>.
//!
//! ## Code Details
//!
//! <inside [`pallet`] module, a template is auto-generated that leads the reader to the relevant items. This is just a reminder to navigate to that page. Don't repeat things like "See Config trait for ..." that are generated inside [`pallet`] in here>
//!
//! See [`pallet`] module.
//!
//! <The audience of this is those who want to know how this pallet works, to the extent of being able to build something on top of it, like a DApp or another pallet>
//!
//! ## Low Level / Implementation Details
//!
//! <The format of this section is up to you, but we suggest the Design-oriented approach that follows>
//!
//! <The audience of this would be your future self, and those who want to deeply understand the pallet to optimize it further and such>
//!
//! ### Design Goals (optional)
//!
//! <Describe your goals with with the pallet design.>
//!
//! ### Design (optional)
//!
//! <Describe how you reach those goals. This should namely describe how your storage is laid out.>
//!
//! ### Terminology (optional)
//!
//! <Optionally, contain any custom terminology here. You can link to it if you want to use the terminology further up>
```

### Dispatchable

For each dispatchable (`fn` item inside `pallet::call`), consider the following template:

```
/// <One liner explaining what this does>
///
/// ## Dispatch Origin
///
/// The dispatch origin of this call must be <details>
///
/// ## Details
///
/// <All other details. Focus on what errors could occur within this dispatch>
///
/// ## Errors (optional)
///
/// <If an extensive list of errors can be returned, list them individually instead of mentioning them in the section above>
///
/// ## Events (optional)
///
/// <Events are akin to the "return type" of dispatchables, optionally mention them>
pub fn name(origin: OriginFor<T>, ...) -> DispatchResult {}
```

### Storage Items

1. If a map-like type is being used, always note the choice of your hashers as private code docs (`// Hasher X chosen because ...`). Recall that this is not relevant information to external people, so it must be documented as `//`.
2. Consider explaining why a storage type is always bounded.
3. Consider explaining the crypto-economics of how a deposit is being taken in return of the storage being used.
