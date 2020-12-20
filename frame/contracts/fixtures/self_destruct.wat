(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_address" (func $seal_address (param i32 i32)))
	(import "seal0" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "seal_terminate" (func $seal_terminate (param i32 i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) reserved for $seal_address output

	;; [32, 36) length of the buffer
	(data (i32.const 32) "\20")

	;; [36, 68) Address of django
	(data (i32.const 36)
		"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04"
		"\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04\04"
	)

	;; [68, 72) reserved for output of $seal_input

	;; [72, 76) length of the buffer
	(data (i32.const 72) "\04")

	;; [76, inf) zero initialized

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
		(call $seal_input (i32.const 68) (i32.const 72))
		(if (i32.load (i32.const 72))
			(then
				(call $seal_address (i32.const 0) (i32.const 32))

				;; Expect address to be 8 bytes.
				(call $assert
					(i32.eq
						(i32.load (i32.const 32))
						(i32.const 32)
					)
				)

				;; Recursively call self with empty input data.
				(call $assert
					(i32.eq
						(call $seal_call
							(i32.const 0)	;; Pointer to own address
							(i32.const 32)	;; Length of own address
							(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
							(i32.const 76)	;; Pointer to the buffer with value to transfer
							(i32.const 8)	;; Length of the buffer with value to transfer
							(i32.const 0)	;; Pointer to input data buffer address
							(i32.const 0)	;; Length of input data buffer
							(i32.const 4294967295) ;; u32 max sentinel value: do not copy output
							(i32.const 0) ;; Length is ignored in this case
						)
						(i32.const 0)
					)
				)
			)
			(else
				;; Try to terminate and give balance to django.
				(call $seal_terminate
					(i32.const 36)	;; Pointer to beneficiary address
					(i32.const 32)	;; Length of beneficiary address
				)
				(unreachable) ;; seal_terminate never returns
			)
		)
	)
)
