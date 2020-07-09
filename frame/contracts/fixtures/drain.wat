(module
	(import "env" "ext_balance" (func $ext_balance (param i32 i32)))
	(import "env" "ext_call" (func $ext_call (param i32 i32 i64 i32 i32 i32 i32 i32 i32) (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 8) reserved for $ext_balance output

	;; [8, 16) length of the buffer
	(data (i32.const 8) "\08")

	;; [16, inf) zero initialized

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
		;; Send entire remaining balance to the 0 address.
		(call $ext_balance (i32.const 0) (i32.const 8))

		;; Balance should be encoded as a u64.
		(call $assert
			(i32.eq
				(i32.load (i32.const 8))
				(i32.const 8)
			)
		)

		;; Self-destruct by sending full balance to the 0 address.
		(call $assert
			(i32.eq
				(call $ext_call
					(i32.const 16)	;; Pointer to destination address
					(i32.const 8)	;; Length of destination address
					(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
					(i32.const 0)	;; Pointer to the buffer with value to transfer
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
)
