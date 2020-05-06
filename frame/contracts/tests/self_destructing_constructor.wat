(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_balance" (func $ext_balance))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
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
		;; Send entire remaining balance to the 0 address.
		(call $ext_balance)

		;; Balance should be encoded as a u64.
		(call $assert
			(i32.eq
				(call $ext_scratch_size)
				(i32.const 8)
			)
		)

		;; Read balance into memory.
		(call $ext_scratch_read
			(i32.const 8)	;; Pointer to write balance to
			(i32.const 0)	;; Offset into scratch buffer
			(i32.const 8)	;; Length of encoded balance
		)

		;; Self-destruct by sending full balance to the 0 address.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 0)	;; Pointer to destination address
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
	)

	(func (export "call"))
)
