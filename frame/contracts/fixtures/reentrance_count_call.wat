;; This fixture recursively tests if reentrance_count returns correct reentrant count value when
;; using seal_call to make caller contract call to itself
(module
	(import "seal0" "seal_input" (func $seal_input (param i32 i32)))
	(import "seal0" "seal_address" (func $seal_address (param i32 i32)))
	(import "seal1" "seal_call" (func $seal_call (param i32 i32 i64 i32 i32 i32 i32 i32) (result i32)))
	(import "seal0" "reentrance_count" (func $reentrance_count (result i32)))
	(import "env" "memory" (memory 1 1))

	;; [0, 32) reserved for $seal_address output

	;; [32, 36) buffer for the call stack height

	;; [36, 40) size of the input buffer
	(data (i32.const 36) "\04")

	;; [40, 44) length of the buffer for $seal_address
	(data (i32.const 40) "\20")

	(func $assert (param i32)
		(block $ok
			(br_if $ok
				(get_local 0)
			)
			(unreachable)
		)
	)
	(func (export "call")
		(local $expected_reentrance_count i32)
		(local $seal_call_exit_code i32)

		;; reading current contract address
		(call $seal_address (i32.const 0) (i32.const 40))

		;; reading passed input
		(call $seal_input (i32.const 32) (i32.const 36))

		;; reading manually passed reentrant count
		(set_local $expected_reentrance_count (i32.load (i32.const 32)))

		;; reentrance count is calculated correctly
		(call $assert
			(i32.eq (call $reentrance_count) (get_local $expected_reentrance_count))
		)

		;; re-enter 5 times in a row and assert that the reentrant counter works as expected
		(i32.eq (call $reentrance_count) (i32.const 5))
		(if
			(then) ;; recursion exit case
			(else
				;; incrementing $expected_reentrance_count passed to the contract
				(i32.store (i32.const 32) (i32.add (i32.load (i32.const 32)) (i32.const 1)))

				;; Call to itself
				(set_local $seal_call_exit_code
					(call $seal_call
						(i32.const 8)	;; Allow reentrancy flag set
						(i32.const 0)	;; Pointer to "callee" address
						(i64.const 0)	;; How much gas to devote for the execution. 0 = all.
						(i32.const 0)	;; Pointer to the buffer with value to transfer
						(i32.const 32)	;; Pointer to input data buffer address
						(i32.const 4)	;; Length of input data buffer
						(i32.const 0xffffffff) ;; u32 max sentinel value: do not copy output
						(i32.const 0) ;; Ptr to output buffer len
					)
				)

				(call $assert
					(i32.eq (get_local $seal_call_exit_code) (i32.const 0))
				)
			)
		)
	)

	(func (export "deploy"))
)