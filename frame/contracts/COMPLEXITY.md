# Complexity

This analysis is on the computing and memory complexity of specific procedures. It provides a rough estimate of operations performed in general and especially focusing on DB reads and writes. It is also an attempt to estimate the memory consumption at its peak.

The primary goal is to come up with decent pricing for functions that can be invoked by a user (via extrinsics) or by untrusted code that prevents DoS attacks.

# Sandboxing

It makes sense to describe the sandboxing module first because the smart-contract module is built upon it.

## Memory

### set

Copies data from the supervisor's memory to the guest's memory.

**complexity**: It doesn't allocate, and the computational complexity is proportional to the number of bytes to copy.

### get

Copies data from the guest's memory to the supervisor's memory.

**complexity**: It doesn't allocate, and the computational complexity is proportional to the number of bytes to copy.

## Instance

### Instantiation

Instantiation of a sandbox module consists of the following steps:

1. Loading the wasm module in the in-memory representation,
2. Performing validation of the wasm code,
3. Setting up the environment which will be used to instantiate the module,
4. Performing the standard wasm instantiation process, which includes (but is not limited to):
    1. Allocating of memory requested by the instance,
    2. Copying static data from the module to newly allocated memory,
    3. Executing the `start` function.

**Note** that the `start` function can be viewed as a normal function and can do anything that a normal function can do, including allocation of more memory or calling the host environment. The complexity of running the `start` function should be considered separately.

In order to start the process of instantiation, the supervisor should provide the wasm module code being instantiated and the environment definition (a set of functions, memories (and maybe globals and tables in the future) available for import by the guest module) for that module. While the environment definition typically is of the constant size (unless mechanisms like dynamic linking are used), the size of wasm is not.

Validation and instantiation in WebAssembly are designed to be able to be performed in linear time. The allocation and computational complexity of loading a wasm module depend on the underlying wasm VM being used. For example, for JIT compilers it can and probably will be non-linear because of compilation. However, for wasmi, it should be linear. We can try to use other VMs that are able to compile code with memory and time consumption proportional to the size of the code.

Since the module itself requests memory, the amount of allocation depends on the module code itself. If untrusted code is being instantiated, it's up to the supervisor to limit the amount of memory available to allocate.

**complexity**: The computational complexity is proportional to the size of wasm code. Memory complexity is proportional to the size of wasm code and the amount of memory requested by the module.

### Preparation to invoke

Invocation of an exported function in the sandboxed module consists of the following steps:

1. Marshalling, copying and unmarshalling the arguments when passing them between the supervisor and executor,
2. Calling into the underlying VM,
3. Marshalling, copying and unmarshalling the result when passing it between the executor and supervisor,

**Note** that the complexity of running the function code itself should be considered separately.

The actual complexity of invocation depends on the underlying VM. Wasmi will reserve a relatively large chunk of memory for the stack before execution of the code, although it's of constant size.

The size of the arguments and the return value depends on the exact function in question, but can be considered as constant.

**complexity**: Memory and computational complexity can be considered as a constant.

### Call from the guest to the supervisor

The executor handles each call from the guest. The execution of it consists of the following steps:

1. Marshalling, copying and unmarshalling the arguments when passing them between the guest and executor,
2. Calling into the supervisor,
3. Marshaling, copying and unmarshalling the result when passing it between the executor and guest.

**Note** that the complexity of running the supervisor handler should be considered separately.

Because calling into the supervisor requires invoking a wasm VM, the actual complexity of invocation depends on the actual VM used for the runtime/supervisor. Wasmi will reserve a relatively large chunk of memory for the stack before execution of the code, although it's of constant size.

The size of the arguments and the return value depends on the exact function in question, but can be considered as a constant.

**complexity**: Memory and computational complexity can be considered as a constant.

# `AccountDb`

`AccountDb` is an abstraction that supports collecting changes to accounts with the ability to efficiently reverting them. Contract
execution contexts operate on the AccountDb. All changes are flushed into underlying storage only after origin transaction succeeds.

## Relation to the underlying storage

At present, `AccountDb` is implemented as a cascade of overlays with the direct storage at the bottom. The direct
storage `AccountDb` leverages child tries. Each overlay is represented by a `Map`. On a commit from an overlay to an
overlay, maps are merged. On commit from an overlay to the bottommost `AccountDb` all changes are flushed to the storage
and on revert, the overlay is just discarded.

> ℹ️ The underlying storage has a overlay layer implemented as a `Map`. If the runtime reads a storage location and the
> respective key doesn't exist in the overlay, then the underlying storage performs a DB access, but the value won't be
> placed into the overlay. The overlay is only filled with writes.
>
> This means that the overlay can be abused in the following ways:
>
> - The overlay can be inflated by issuing a lot of writes to unique locations,
> - Deliberate cache misses can be induced by reading non-modified storage locations,

It also worth noting that the performance degrades with more state stored in the trie. Due to this
there is not negligible chance that gas schedule will be updated for all operations that involve
storage access.

## get_storage, get_code_hash, get_rent_allowance, get_balance, contract_exists

These functions check the local cache for a requested value and, if it is there, the value is returned. Otherwise, these functions will ask an underlying `AccountDb`  for the value. This means that the number of lookups is proportional to the depth of the overlay cascade. If the value can't be found before reaching the bottommost `AccountDb`, then a DB read will be performed (in case `get_balance` the function `free_balance` will be invoked).

A lookup in the local cache consists of at least one `Map` lookup, for locating the specific account. For `get_storage` there is a second lookup: because account's storage is implemented as a nested map, another lookup is required for fetching a storage value by a key.

These functions return an owned value as its result, so memory usage depends on the value being returned.

**complexity**: The memory complexity is proportional to the size of the value. The computational complexity is proportional to the depth of the overlay cascade and the size of the value; the cost is dominated by the DB read though.

## set_storage, set_balance, set_rent_allowance

These functions only modify the local `Map`.

A lookup in the local cache consists of at least one `Map` lookup, for locating the specific account. For `get_storage` there is a second lookup: because account's storage is implemented as a nested map, another lookup is required for fetching a storage value by a key.

While these functions only modify the local `Map`, if changes made by them are committed to the bottommost `AccountDb`, each changed entry in the `Map` will require a DB write. Moreover, if the balance of the account is changed to be below `existential_deposit` then that account along with all its storage will be removed, which requires time proportional to the number of storage entries that account has. It should be ensured that pricing accounts for these facts.

**complexity**: Each lookup has a logarithmical computing time to the number of already inserted entries. No additional memory is required.

## instantiate_contract

Calls `contract_exists` and if it doesn't exist, do not modify the local `Map` similarly to `set_rent_allowance`.

**complexity**: The computational complexity is proportional to the depth of the overlay cascade and the size of the value; the cost is dominated by the DB read though. No additional memory is required.

## commit

In this function, all cached values will be inserted into the underlying `AccountDb` or into the storage.

We are doing `N` inserts into `Map` (`O(log M)` complexity) or into the storage, where `N` is the size of the committed `Map` and `M` is the size of the map of the underlying overlay. Consider adjusting the price of modifying the `AccountDb` to account for this (since pricing for the count of entries in `commit` will make the price of commit way less predictable). No additional memory is required.

Note that in case of storage modification we need to construct a key in the underlying storage. In order to do that we need:

- perform `twox_128` hashing over a concatenation of some prefix literal and the `AccountId` of the storage owner.
- then perform `blake2_256` hashing of the storage key.
- concatenation of these hashes will constitute the key in the underlying storage.

There is also a special case to think of: if the balance of some account goes below `existential_deposit`, then all storage entries of that account will be erased, which requires time proportional to the number of storage entries that account has.

**complexity**: `N` inserts into a `Map` or eventually into the storage (if committed). Every deleted account will induce removal of all its storage which is proportional to the number of storage entries that account has.

## revert

Consists of dropping (in the Rust sense) of the `AccountDb`.

**complexity**: Computing complexity is proportional to a number of changed entries in a overlay. No additional memory is required.

# Executive

## Transfer

This function performs the following steps:

1. Querying source and destination balances from an overlay (see `get_balance`),
2. Querying `existential_deposit`.
3. Executing `ensure_account_liquid` hook.
4. Updating source and destination balance in the overlay (see `set_balance`).

**Note** that the complexity of executing `ensure_account_liquid` hook should be considered separately.

In the course of the execution this function can perform up to 2 DB reads to `get_balance` of source and destination accounts. It can also induce up to 2 DB writes via `set_balance` if flushed to the storage.

Moreover, if the source balance goes below `existential_deposit`  then the transfer is denied and
returns with an error.

Assuming marshaled size of a balance value is of the constant size we can neglect its effect on the performance.

**complexity**: up to 2 DB reads and up to 2 DB writes (if flushed to the storage) in the standard case. If removal of the source account takes place then it will additionally perform a DB write per one storage entry that the account has. For the current `AccountDb` implementation computing complexity also depends on the depth of the `AccountDb` cascade. Memorywise it can be assumed to be constant.

## Initialization

Before a call or instantiate can be performed the execution context must be initialized.

For the first call or instantiation in the handling of an extrinsic, this involves two calls:

1. `<timestamp::Module<T>>::now()`
2. `<system::Module<T>>::block_number()`

The complexity of initialization depends on the complexity of these functions. In the current
implementation they just involve a DB read.

For subsequent calls and instantiations during contract execution, the initialization requires no
expensive operations.

## Terminate

This function performs the following steps:

1. Check the calling contract is not already on the callstack by calling `is_live`.
2. `transfer` funds from caller to the beneficiary.
3. Flag the caller contract as deleted in the overlay.

`is_live` does not do any database access nor does it allocate memory. It walks up the call
stack and therefore executes in linear time depending on size of the call stack. Because
the call stack is of a fixed maximum size we consider this operation as constant time.

**complexity**: Database accesses as described in Transfer + Removal of the contract. Currently,
we are using child trie removal which is linear in the amount of stored keys. Upcoming changes
will make the account removal constant time.


## Call

This function receives input data for the contract execution. The execution consists of the following steps:

1. Initialization of the execution context.
2. Checking rent payment.
3. Loading code from the DB.
4. `transfer`-ing funds between the caller and the destination account.
5. Executing the code of the destination account.
6. Committing overlayed changed to the underlying `AccountDb`.

**Note** that the complexity of executing the contract code should be considered separately.

Checking for rent involves 2 unconditional DB reads: `ContractInfoOf` and `block_number`
and on top of that at most once per block:

- DB read to `free_balance` and
- `rent_deposit_offset` and
- `rent_byte_price` and
- `Currency::minimum_balance` and
- `tombstone_deposit`.
- Calls to `ensure_can_withdraw`, `withdraw`, `make_free_balance_be` can perform arbitrary logic and should be considered separately,
- `child_storage_root`
- `kill_child_storage`
- mutation of `ContractInfoOf`

Loading code most likely will trigger a DB read, since the code is immutable and therefore will not get into the cache (unless a suicide removes it, or it has been instantiated in the same call chain).

Also, `transfer` can make up to 2 DB reads and up to 2 DB writes (if flushed to the storage) in the standard case. If removal of the source account takes place then it will additionally perform a DB write per one storage entry that the account has.

Finally, all changes are `commit`-ted into the underlying overlay. The complexity of this depends on the number of changes performed by the code. Thus, the pricing of storage modification should account for that.

**complexity**:
- Only for the first invocation of the contract: up to 5 DB reads and one DB write as well as logic executed by `ensure_can_withdraw`, `withdraw`, `make_free_balance_be`.
- On top of that for every invocation: Up to 5 DB reads. DB read of the code is of dynamic size. There can also be up to 2 DB writes (if flushed to the storage). Additionally, if the source account removal takes place a DB write will be performed per one storage entry that the account has.

## Instantiate

This function takes the code of the constructor and input data. Instantiation of a contract consists of the following steps:

1. Initialization of the execution context.
2. Calling `DetermineContractAddress` hook to determine an address for the contract,
3. `transfer`-ing funds between self and the newly instantiated contract.
4. Executing the constructor code. This will yield the final code of the code.
5. Storing the code for the newly instantiated contract in the overlay.
6. Committing overlayed changed to the underlying `AccountDb`.

**Note** that the complexity of executing the constructor code should be considered separately.

**Note** that the complexity of `DetermineContractAddress` hook should be considered separately as well. Most likely it will use some kind of hashing over the code of the constructor and input data. The default `SimpleAddressDeterminer` does precisely that.

**Note** that the constructor returns code in the owned form and it's obtained via return facilities, which should have take fee for the return value.

Also, `transfer` can make up to 2 DB reads and up to 2 DB writes (if flushed to the storage) in the standard case. If removal of the source account takes place then it will additionally perform a DB write per one storage entry that the account has.

Storing the code in the overlay may induce another DB write (if flushed to the storage) with the size proportional to the size of the constructor code.

Finally, all changes are `commit`-ted into the underlying overlay. The complexity of this depends on the number of changes performed by the constructor code. Thus, the pricing of storage modification should account for that.

**complexity**: Up to 2 DB reads and induces up to 3 DB writes (if flushed to the storage), one of which is dependent on the size of the code. Additionally, if the source account removal takes place a DB write will be performed per one storage entry that the account has.

# Externalities

Each external function invoked from a contract can involve some overhead.

## ext_gas

**complexity**: This is of constant complexity.

## ext_set_storage

This function receives a `key` and `value` as arguments. It consists of the following steps:

1. Reading the sandbox memory for `key` and `value` (see sandboxing memory get).
2. Setting the storage at the given `key` to the given `value` (see `set_storage`).

**complexity**: Complexity is proportional to the size of the `value`. This function induces a DB write of size proportional to the `value` size (if flushed to the storage), so should be priced accordingly.

## ext_clear_storage

This function receives a `key` as argument. It consists of the following steps:

1. Reading the sandbox memory for `key` (see sandboxing memory get).
2. Clearing the storage at the given `key` (see `set_storage`).

**complexity**: Complexity is constant. This function induces a DB write to clear the storage entry
(upon being flushed to the storage) and should be priced accordingly.

## ext_get_storage

This function receives a `key` as an argument. It consists of the following steps:

1. Reading the sandbox memory for `key` (see sandboxing memory get).
2. Reading the storage with the given key (see `get_storage`). It receives back the owned result buffer.
3. Replacing the scratch buffer.

Key is of a constant size. Therefore, the sandbox memory load can be considered to be of constant complexity.

Unless the value is cached, a DB read will be performed. The size of the value is not known until the read is
performed. Moreover, the DB read has to be synchronous and no progress can be made until the value is fetched.

**complexity**: The memory and computing complexity is proportional to the size of the fetched value. This function performs a
DB read.

## ext_transfer

This function receives the following arguments:

- `account` buffer of a marshaled `AccountId`,
- `value` buffer of a marshaled `Balance`,

It consists of the following steps:

1. Loading `account` buffer from the sandbox memory (see sandboxing memory get) and then decoding it.
2. Loading `value` buffer from the sandbox memory and then decoding it.
4. Invoking the executive function `transfer`.

Loading of `account` and `value` buffers should be charged. This is because the sizes of buffers are specified by the calling code, even though marshaled representations are, essentially, of constant size. This can be fixed by assigning an upper bound for sizes of `AccountId` and `Balance`.

## ext_call

This function receives the following arguments:

- `callee` buffer of a marshaled `AccountId`,
- `gas` limit which is plain u64,
- `value` buffer of a marshaled `Balance`,
- `input_data`. An arbitrarily sized byte vector.

It consists of the following steps:

1. Loading `callee` buffer from the sandbox memory (see sandboxing memory get) and then decoding it.
2. Loading `value` buffer from the sandbox memory and then decoding it.
3. Loading `input_data` buffer from the sandbox memory.
4. Invoking the executive function `call`.

Loading of `callee` and `value` buffers should be charged. This is because the sizes of buffers are specified by the calling code, even though marshaled representations are, essentially, of constant size. This can be fixed by assigning an upper bound for sizes of `AccountId` and `Balance`.

Loading `input_data` should be charged in any case.

**complexity**: All complexity comes from loading buffers and executing `call` executive function. The former component is proportional to the sizes of `callee`, `value` and `input_data` buffers. The latter component completely depends on the complexity of `call` executive function, and also dominated by it.

## ext_instantiate

This function receives the following arguments:

- `init_code`, a buffer which contains the code of the constructor.
- `gas` limit which is plain u64
- `value` buffer of a marshaled `Balance`
- `input_data`. an arbitrarily sized byte vector.

It consists of the following steps:

1. Loading `init_code` buffer from the sandbox memory (see sandboxing memory get) and then decoding it.
2. Loading `value` buffer from the sandbox memory and then decoding it.
3. Loading `input_data` buffer from the sandbox memory.
4. Invoking `instantiate` executive function.

Loading of `value` buffer should be charged. This is because the size of the buffer is specified by the calling code, even though marshaled representation is, essentially, of constant size. This can be fixed by assigning an upper bound for size for `Balance`.

Loading `init_code` and `input_data` should be charged in any case.

**complexity**: All complexity comes from loading buffers and executing `instantiate` executive function. The former component is proportional to the sizes of `init_code`, `value` and `input_data` buffers. The latter component completely depends on the complexity of `instantiate` executive function and also dominated by it.

## ext_terminate

This function receives the following arguments:

- `beneficiary`, buffer of a marshaled `AccountId`

It consists of the following steps:

1. Loading `beneficiary` buffer from the sandbox memory (see sandboxing memory get) and then decoding it.

Loading of the `beneficiary` buffer should be charged. This is because the sizes of buffers are specified by the calling code, even though marshaled representations are, essentially, of constant size. This can be fixed by assigning an upper bound for sizes of `AccountId`.

**complexity**: All complexity comes from loading buffers and executing `terminate` executive function. The former component is proportional to the size of the `beneficiary` buffer. The latter component completely depends on the complexity of `terminate` executive function and also dominated by it.

## ext_return

This function receives a `data` buffer as an argument. Execution of the function consists of the following steps:

1. Loading `data` buffer from the sandbox memory (see sandboxing memory get),
2. Trapping

**complexity**: The complexity of this function is proportional to the size of the `data` buffer.

## ext_deposit_event

This function receives a `data` buffer as an argument. Execution of the function consists of the following steps:

1. Loading `data` buffer from the sandbox memory (see sandboxing memory get),
2. Insert to nested context execution
3. Copies from nested to underlying contexts
4. Call system deposit event

**complexity**: The complexity of this function is proportional to the size of the `data` buffer.

## ext_caller

This function serializes the address of the caller into the scratch buffer.

**complexity**: Assuming that the address is of constant size, this function has constant complexity.

## ext_random

This function serializes a random number generated by the given subject into the scratch buffer.
The complexity of this function highly depends on the complexity of `System::random`. `max_subject_len`
limits the size of the subject buffer.

**complexity**: The complexity of this function depends on the implementation of `System::random`.

## ext_now

This function serializes the current block's timestamp into the scratch buffer.

**complexity**: Assuming that the timestamp is of constant size, this function has constant complexity.

## ext_scratch_size

This function returns the size of the scratch buffer.

**complexity**: This function is of constant complexity.

## ext_scratch_read

This function copies slice of data from the scratch buffer to the sandbox memory. The calling code specifies the slice length. Execution of the function consists of the following steps:

1. Storing a specified slice of the scratch buffer into the sandbox memory (see sandboxing memory set)

**complexity**: The computing complexity of this function is proportional to the length of the slice. No additional memory is required.

## ext_scratch_write

This function copies slice of data from the sandbox memory to the scratch buffer. The calling code specifies the slice length. Execution of the function consists of the following steps:

1. Loading a slice from the sandbox memory into the (see sandboxing memory get)

**complexity**: Complexity is proportional to the length of the slice.

## ext_set_rent_allowance

This function receives the following argument:

- `value` buffer of a marshaled `Balance`,

It consists of the following steps:

1. Loading `value` buffer from the sandbox memory and then decoding it.
2. Invoking `set_rent_allowance` AccountDB function.

**complexity**: Complexity is proportional to the size of the `value`. This function induces a DB write of size proportional to the `value` size (if flushed to the storage), so should be priced accordingly.

## ext_rent_allowance

It consists of the following steps:

1. Invoking `get_rent_allowance` AccountDB function.
2. Serializing the rent allowance of the current contract into the scratch buffer.

**complexity**: Assuming that the rent allowance is of constant size, this function has constant complexity. This
function performs a DB read.

## ext_block_number

This function serializes the current block's number into the scratch buffer.

**complexity**: Assuming that the block number is of constant size, this function has constant complexity.

## Built-in hashing functions

This paragraph concerns the following supported built-in hash functions:

- `SHA2` with 256-bit width
- `KECCAK` with 256-bit width
- `BLAKE2` with 128-bit and 256-bit widths

These functions compute a cryptographic hash on the given inputs and copy the
resulting hash directly back into the sandboxed Wasm contract output buffer.

Execution of the function consists of the following steps:

1. Load data stored in the input buffer into an intermediate buffer.
2. Compute the cryptographic hash `H` on the intermediate buffer.
3. Copy back the bytes of `H` into the contract side output buffer.

**complexity**: Complexity is proportional to the size of the input buffer in bytes
as well as to the size of the output buffer in bytes. Also different cryptographic
algorithms have different inherent complexity so users must expect the above
mentioned crypto hashes to have varying gas costs.
The complexity of each cryptographic hash function highly depends on the underlying
implementation.
