(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_get_storage" (func $seal_get_storage (param i32 i32 i32) (result i32)))
	(import "seal0" "seal_set_storage" (func $seal_set_storage (param i32 i32 i32)))
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_transfer" (func $seal_transfer (param i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_instantiate" (func $seal_instantiate (param i32 i32 i64 i32 i32 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) Endowment to send when creating contract.
	(data (i32.const 0) "\00\00\01")

	;; [8, 16) Value to send when calling contract.

	;; [16, 48) The key to store the contract address under.

	;; [48, 80) Buffer where to store the input to the contract

	;; [80, 88) Buffer where to store the address of the instantiated contract

	;; [88, 96) Size of the buffer
	(data (i32.const 88) "\08")

	;; [96, 100) Size of the input buffer
	(data (i32.const 96) "\20")

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
		(call $seal_input (i32.const 48) (i32.const 96))
		(call $assert
			(i32.eq
				(i32.load (i32.const 96))
				(i32.const 32)
			)
		)

		;; Deploy the contract with the provided code hash.
		(call $assert
			(i32.eq
				(call $seal_instantiate
					(i32.const 48)	;; Pointer to the code hash.
					(i32.const 32)	;; Length of the code hash.
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer.
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
					(i32.const 80)	;; Buffer where to store address of new contract
					(i32.const 88)	;; Pointer to the length of the buffer
					(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
					(i32.const 0) ;; Length is ignored in this cas
				)
				(i32.const 0)
			)
		)

		;; Check that address has expected length
		(call $assert
			(i32.eq
				(i32.load (i32.const 88))
				(i32.const 8)
			)
		)

		;; Store the return address.
		(call $seal_set_storage
			(i32.const 16)	;; Pointer to the key
			(i32.const 80)	;; Pointer to the value
			(i32.const 8)	;; Length of the value
		)
	)

	(func (export "call")
		;; Read address of destination contract from storage.
		(call $assert
			(i32.eq
				(call $seal_get_storage
					(i32.const 16)	;; Pointer to the key
					(i32.const 80)	;; Pointer to the value
					(i32.const 88)	;; Pointer to the len of the value
				)
				(i32.const 0)
			)
		)
		(call $assert
			(i32.eq
				(i32.load (i32.const 88))
				(i32.const 8)
			)
		)

		;; Calling the destination contract with non-empty input data should fail.
		(call $assert
			(i32.eq
				(call $seal_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 1)	;; Length of input data buffer
					(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
					(i32.const 0) ;; Length is ignored in this case

				)
				(i32.const 0x1)
			)
		)

		;; Call the destination contract regularly, forcing it to self-destruct.
		(call $assert
			(i32.eq
				(call $seal_call
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 8)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
					(i32.const 0)	;; Pointer to input data buffer address
					(i32.const 0)	;; Length of input data buffer
					(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
					(i32.const 0) ;; Length is ignored in this case
				)
				(i32.const 0)
			)
		)

		;; Calling the destination address with non-empty input data should now work since the
		;; contract has been removed. Also transfer a balance to the address so we can ensure this
		;; does not keep the contract alive.
		(call $assert
			(i32.eq
				(call $seal_transfer
					(i32.const 80)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i32.const 0)	;; Pointer to the buffer with value to transfer
					(i32.const 8)	;; Length of the buffer with value to transfer
				)
				(i32.const 0)
			)
		)
	)
)
