(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_get_storage" (func $ext_get_storage (param i32) (result i32)))
	(import "env" "ext_set_storage" (func $ext_set_storage (param i32 i32 i32)))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_instantiate" (func $ext_instantiate (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy")
	;; Input data is the code hash of the contract to be deployed.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 32)
			)
		)

		;; Copy code hash from scratch buffer into this contract's memory.
		(call $ext_scratch_read
			(i32.const 48)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 32)		;; Count of bytes to copy.
		)

		;; Deploy the contract with the provided code hash.
		(call $assert
			(i32.eq
				(call $ext_instantiate
					(i32.const 48)	;; Pointer to the code hash.
					(i32.const 32)	;; Length of the code hash.
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer.
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)

		;; Read the address of the instantiated contract into memory.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)
		(call $ext_scratch_read
			(i32.const 80)		;; The pointer where to store the scratch buffer contents,
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Store the return address.
		(call $ext_set_storage
			(i32.const 16)	;; Pointer to the key
			(i32.const 80)	;; Pointer to the value
			(i32.const 8)	;; Length of the value
		)
	)

	(func (export "call")
		;; Read address of destination contract from storage.
		(call $assert
			(i32.eq
				(call $ext_get_storage
					(i32.const 16)	;; Pointer to the key
				)
				(i32.const 0)
			)
		)
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)
		(call $ext_scratch_read
			(i32.const 80)		;; The pointer where to store the contract address.
			(i32.const 0)		;; Offset from the start of the scratch buffer.
			(i32.const 8)		;; Count of bytes to copy.
		)

		;; Calling the destination contract with non-empty input data should fail.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 1)	;; Length of input data buffer
				)
				(i32.const 0x0100)
			)
		)

		;; Call the destination contract regularly, forcing it to self-destruct.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 8)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)

		;; Calling the destination address with non-empty input data should now work since the
		;; contract has been removed. Also transfer a balance to the address so we can ensure this
		;; does not keep the contract alive.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 1)	;; Length of input data buffer
				)
				(i32.const 0)
			)
		)
	)

	(data (i32.const 0) "\00\00\01")		;; Endowment to send when creating contract.
	(data (i32.const 8) "")		;; Value to send when calling contract.
	(data (i32.const 16) "")	;; The key to store the contract address under.
)
