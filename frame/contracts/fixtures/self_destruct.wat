(module
	(import "env" "ext_scratch_size" (func $ext_scratch_size (result i32)))
	(import "env" "ext_scratch_read" (func $ext_scratch_read (param i32 i32 i32)))
	(import "env" "ext_address" (func $ext_address))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32) (result i32)))
	(import "env" "ext_terminate" (func $ext_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)

	(func (export "deploy"))

	(func (export "call")
		;; If the input data is not empty, then recursively call self with empty input data.
		;; This should trap instead of self-destructing since a contract cannot be removed live in
		;; the execution stack cannot be removed. If the recursive call traps, then trap here as
		;; well.
		(if (call $ext_scratch_size)
			(then
				(call $ext_address)

				;; Expect address to be 8 bytes.
				(call $assert
					(i32.eq
						(call $ext_scratch_size)
						(i32.const 8)
					)
				)

				;; Read own address into memory.
				(call $ext_scratch_read
					(i32.const 16)	;; Pointer to write address to
					(i32.const 0)	;; Offset into scratch buffer
					(i32.const 8)	;; Length of encoded address
				)

				;; Recursively call self with empty input data.
				(call $assert
					(i32.eq
						(call $ext_call
							(i32.const 16)	;; Pointer to own address
							(i32.const 8)	;; Length of own address
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
			(else
				;; Try to terminate and give balance to django.
				(call $ext_terminate
					(i32.const 32)	;; Pointer to beneficiary address
					(i32.const 8)	;; Length of beneficiary address
				)
				(unreachable) ;; ext_terminate never returns
			)
		)
	)
	;; Address of django
	(data (i32.const 32) "\04\00\00\00\00\00\00\00")
)
