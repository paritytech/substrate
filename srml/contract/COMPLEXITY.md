# Sandboxing

It makes sense to describe the sandboxing module first because the smart-contract module is built upon it.

## Memory

### set

Copies data from the supervisor's memory to the guest's memory.

**complexity** It doesn't allocate, and compute complexity is proportional to the number of bytes to copy.

### get

Copies data from the guest's memory to the supervisor's memory.

**complexity**: It doesn't allocate, and compute complexity is proportional to the number of bytes to copy.

## Instance

### Instantiation

Instantiation of a sandbox module consists of the following steps:

1. Loading wasm module in the in-memory representation,
2. Performing validation of wasm code,
3. Setting up the environment which will be used to instantiate a module,
4. Run instantiation process, which includes (but not limited to):
	1. Allocation of memory requested by the instance,
	2. Copying static data from the module to newly allocated memory,
	3. Executing `start` function.

**Note** that `start` function can be viewed as a normal function and can do anything that normal function can do, including allocation of more memory or calling the environment. The complexity of running `start` function should be considered separately.

In order to start the process of instantiation, the supervisor should provide the wasm module code being instantiated and the environment definition (a set of functions, memories (and maybe globals and tables in the future) available for import by the guest module) for that module. While the environment definition typically is of the constant size (unless mechanisms like dynamic linking are used), the size of wasm is not.

The allocation and compute complexity of loading wasm module depends on the underlying wasm VM being used. For example, the size and compute time for JIT compilers can be non-linear, because of compilation. However, for wasmi it should be linear. As per validation and instantiation, in WebAssembly they are designed to be able to be performed in linear time.

Since it is the module what requests memory, amount of allocation depends on the module code itself. If an untrusted code is being instantiated, it's up to the supervisor to limit the amount of memory available to allocate.

**complexity**: Compute complexity is *typically* proportional to the size of wasm code. Memory complexity is *typically* proportional to the size of wasm code and the amount of memory requested by the module itself.

### Preparation to invoke

Invocation of an exported function in the sandboxed module consists of the following steps:

1. Marshalling, copying and unmarshalling the arguments when passing them between the supervisor and executor,
2. Calling into the underlying VM,
3. Marshalling, copying and unmarshalling the result when passing it between the executor and supervisor,

**Note** that the complexity of running the function code itself should be considered separately.

The actual complexity of invocation depends on the underlying VM. Wasmi will reserve a relatively large chunk of memory for the stack before execution of the code, although it's of constant size.

The size of the arguments and the return value depends on the exact function in question and typically can be considered as constant.

**complexity**: Memory and compute complexity *typically* can be considered as a constant.

### Call from the guest to the supervisor

Each call from the guest is handled by the executor and consists of the following steps:

1. Marshalling, copying and unmarshalling the arguments when passing them between the guest and executor,
2. Calling into the supervisor,
3. Marshalling, copying and unmarshalling the result when passing it between the executor and guest.

**Note** that the complexity of running the supervisor handler should be considered separately.

Because calling into the supervisor requires invoking a wasm VM, the actual complexity of invocation depends on the actual VM used for the runtime/supervisor. Wasmi will reserve a relatively large chunk of memory for the stack before execution of the code, although it's of constant size.

The size of the arguments and the return value depends on the exact function in question and typically can be considered as a constant.

**complexity**: Memory and compute complexity *typically* can be considered as a constant.

# AccountDb

AccountDb is an abstraction that supports collecting changes to accounts with the ability to efficiently reverting them. Contract
execution contexts operate on the AccountDb. All changes are flushed into underlying storage only after origin transaction succeeds.

## get_storage

TODO:

## set_storage

TODO:

## get_code

TODO:

## set_code

TODO:

## get_balance

TODO:

## set_balance

TODO:

## commit

TODO:

## revert

TODO:

# Contract Runtime

## Transfer

This function performs the following steps:

1. Queries source and destination balance from an overlay,
2. Queries `existential_deposit`. This hits DB unless cached.
3. Executes `ensure_account_liquid` hook.
4. Updates source balance in the overlay.

**Note** that the complexity of executing `ensure_account_liquid` hook should be considered separately.

TODO: This depends on account db complexity get_balance / set_balance

## Call

TODO: Depends on transfer

## Create

TODO: Depends on transfer

# Externalities

## ext_set_storage

...