Provides types and traits for creating and checking inherents.

Each inherent is added to a produced block. Each runtime decides on which inherents it
wants to attach to its blocks. All data that is required for the runtime to create the inherents
is stored in the `InherentData`. This `InherentData` is constructed by the node and given to
the runtime.

Types that provide data for inherents, should implement `InherentDataProvider` and need to be
registered at `InherentDataProviders`.

In the runtime, modules need to implement `ProvideInherent` when they can create and/or check
inherents. By implementing `ProvideInherent`, a module is not enforced to create an inherent.
A module can also just check given inherents. For using a module as inherent provider, it needs
to be registered by the `construct_runtime!` macro. The macro documentation gives more
information on how that is done.

License: Apache-2.0